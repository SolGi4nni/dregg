//! Bridge from turn-level `Effect` to circuit-level `dregg_circuit::effect_vm::Effect`.
//!
//! This module owns the (intentionally lossy) projection of a `Turn` into the
//! sequence of VM effects that the Effect VM AIR consumes for STARK proving.

use dregg_cell::CellId;

use crate::action::Effect;
use crate::forest::CallTree;
use crate::turn::Turn;

pub(super) fn convert_turn_effects_to_vm(
    cell_id: &CellId,
    turn: &Turn,
) -> Vec<dregg_circuit::effect_vm::Effect> {
    fn collect_effects(
        tree: &CallTree,
        cell_id: &CellId,
        vm_effects: &mut Vec<dregg_circuit::effect_vm::Effect>,
    ) {
        use dregg_circuit::effect_vm::Effect as VmEffect;
        use dregg_circuit::field::BabyBear;

        // CLOSED (effect-vm-hash-truncation lane, 2026-05-28): both helpers
        // previously took ONLY the first 4 bytes of each 32-byte value
        // (P1-2 in AUDIT-turn-executor.md), so the EffectVM proof bound only
        // 4 bytes of each hash/field element — two effects differing solely
        // in bytes [4..32] collapsed to the same circuit-side identifier and
        // produced interchangeable proofs.
        //
        // Both helpers now delegate to the SHARED canonical fold
        // `dregg_circuit::effect_vm::fold_bytes32_to_bb`, which Horner-folds
        // all 8 four-byte limbs of the value into the BabyBear felt. The SDK
        // projector (`sdk/src/cipherclerk.rs::convert_effects_to_vm`) imports
        // and calls the SAME function, so the two projectors agree byte-for-
        // byte by construction (asserted by the differential invariant in
        // `protocol-tests/.../effect_vm_differential.rs`). Because every byte
        // now contributes to the felt, the per-effect param column and the
        // `compute_effects_hash`-derived `PI[EFFECTS_HASH]` bind the full
        // 32-byte value rather than a 4-byte equivalence class.
        //
        // (The full-u64 amount truncation, by contrast, was closed earlier:
        // the VM effect carries `value_full` bound via 4×16-bit PI limbs +
        // effects_hash, and the note-spending spend proof now binds the full
        // u64 via the VALUE_HI column — see apply.rs + dsl::note_spending.)
        fn hash_to_bb(h: &[u8; 32]) -> BabyBear {
            dregg_circuit::effect_vm::fold_bytes32_to_bb(h)
        }

        fn field_element_to_bb(value: &[u8; 32]) -> BabyBear {
            dregg_circuit::effect_vm::fold_bytes32_to_bb(value)
        }

        // 32-byte widening (effect-vm-hash-widen lane, 2026-05-28): the full
        // 256-bit binding path. Projects a 32-byte value into 8 BabyBear limbs
        // (4 bytes each, little-endian) via the SHARED circuit helper, so the
        // executor and SDK projectors emit byte-for-byte identical encodings
        // (asserted by the protocol-tests differential invariant). Used for the
        // hash params widened to `[BabyBear; 8]` — same shape EmitEvent/Custom
        // already use. Where the old single-felt fold gave ~31-bit collision
        // resistance, the 8-limb form binds all 32 bytes via compute_effects_hash.
        fn hash_to_8(h: &[u8; 32]) -> [BabyBear; 8] {
            dregg_circuit::effect_vm::bytes32_to_8_limbs(h)
        }

        for effect in &tree.action.effects {
            match effect {
                Effect::Transfer { from, to, amount } => {
                    if from == cell_id {
                        vm_effects.push(VmEffect::Transfer {
                            amount: *amount,
                            direction: 1,
                        });
                    } else if to == cell_id {
                        vm_effects.push(VmEffect::Transfer {
                            amount: *amount,
                            direction: 0,
                        });
                    }
                }
                Effect::SetField { cell, index, value } if cell == cell_id => {
                    vm_effects.push(VmEffect::SetField {
                        field_idx: *index as u32,
                        value: field_element_to_bb(value),
                    });
                }
                Effect::GrantCapability { to, cap, .. } if to == cell_id => {
                    let cap_hash = blake3::hash(&cap.slot.to_le_bytes());
                    vm_effects.push(VmEffect::GrantCapability {
                        cap_entry: hash_to_8(cap_hash.as_bytes()),
                        // Legacy direction-0 recipient-install row (this arm
                        // matches `to == cell_id`); the Phase-B2 granter-side
                        // delegation row (`Some`) is built at the prover site.
                        phase_b: None,
                    });
                }
                Effect::NoteSpend {
                    nullifier, value, ..
                } => {
                    vm_effects.push(VmEffect::NoteSpend {
                        nullifier: hash_to_bb(&nullifier.0),
                        value: *value,
                    });
                }
                Effect::NoteCreate {
                    commitment, value, ..
                } => {
                    vm_effects.push(VmEffect::NoteCreate {
                        commitment: hash_to_bb(&commitment.0),
                        value: *value,
                    });
                }
                Effect::IncrementNonce { cell } if cell == cell_id => {
                    vm_effects.push(VmEffect::IncrementNonce);
                }

                // ====================================================
                // Stage 1 (D): wire up the 7 runtime variants whose AIR
                // counterparts already exist but were previously mapped
                // to NoOp. The AIR enforces the per-effect arithmetic;
                // the projection is no longer lossy for these.
                // ====================================================
                Effect::MakeSovereign { cell } if cell == cell_id => {
                    vm_effects.push(VmEffect::MakeSovereign);
                }
                Effect::CreateCellFromFactory {
                    factory_vk,
                    owner_pubkey,
                    ..
                } => {
                    vm_effects.push(VmEffect::CreateCellFromFactory {
                        factory_vk: hash_to_bb(factory_vk),
                        child_vk_derived: hash_to_bb(owner_pubkey),
                    });
                }

                // ====================================================
                // Stage 3 complete: the 22 runtime variants below all
                // have real per-variant AIR coverage. Each projects to
                // a real VmEffect with its own constraint shape
                // (passthrough, balance debit/credit, or cap_root
                // transition). See STAGE-3-AIR-PLAN.md for the per-
                // variant rationale and EFFECT-VM-SHAPE-A.md for the
                // master plan context.
                // ====================================================
                Effect::SetPermissions {
                    cell,
                    new_permissions,
                } if cell == cell_id => {
                    // Stage 3: real AIR coverage. Permissions aren't in
                    // VM state; bind their hash into effects_hash.
                    let perm_bytes = postcard::to_allocvec(new_permissions).unwrap_or_default();
                    let perm_hash_bytes = blake3::hash(&perm_bytes);
                    vm_effects.push(VmEffect::SetPermissions {
                        permissions_hash: hash_to_8(perm_hash_bytes.as_bytes()),
                    });
                }
                Effect::SetVerificationKey { cell, new_vk } if cell == cell_id => {
                    // Stage 3: real AIR coverage. VK lives off-trace;
                    // bind its hash into effects_hash. None → all-zero limbs.
                    let vk_hash = match new_vk {
                        Some(vk) => {
                            let bytes = postcard::to_allocvec(vk).unwrap_or_default();
                            let h = blake3::hash(&bytes);
                            hash_to_8(h.as_bytes())
                        }
                        None => [dregg_circuit::field::BabyBear::ZERO; 8],
                    };
                    vm_effects.push(VmEffect::SetVerificationKey { vk_hash });
                }
                Effect::RevokeCapability { cell, slot } if cell == cell_id => {
                    // Stage 3: real AIR coverage. Mirrors GrantCapability.
                    // The slot's bytes are hashed and limb[0] is mixed into
                    // capability_root deterministically by the AIR.
                    let slot_bytes = slot.to_le_bytes();
                    let slot_hash_bytes = blake3::hash(&slot_bytes);
                    vm_effects.push(VmEffect::RevokeCapability {
                        slot_hash: hash_to_8(slot_hash_bytes.as_bytes()),
                        phase_b: None,
                    });
                }
                Effect::CreateCell {
                    public_key,
                    token_id,
                    balance,
                } => {
                    // Stage 3: real AIR coverage. CreateCell rejects
                    // non-zero balance via executor, so the actor's
                    // balance doesn't change — passthrough is correct.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(public_key);
                    hasher.update(token_id);
                    hasher.update(&balance.to_le_bytes());
                    let create_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::CreateCell {
                        create_hash: hash_to_8(create_hash_bytes.as_bytes()),
                    });
                }

                Effect::EmitEvent { cell, event } if cell == cell_id => {
                    // Stage 3 + #110: real AIR coverage with canonical
                    // (topic_hash, payload_hash) binding. Each 32-byte
                    // BLAKE3 hash projects into 8 BabyBear felts via
                    // 4-bytes-per-felt little-endian packing (matches the
                    // Custom::program_vk_hash convention).
                    //
                    // - topic_hash = BLAKE3(event.topic)        (32 bytes)
                    // - payload_hash = BLAKE3(event.data ‖ ...) (32 bytes)
                    //
                    // The AIR's per-row PI-equality constraint pins the low 4
                    // felts of each into params[0..8]; effects_hash absorbs
                    // all 16 felts (cryptographic high-half binding); the
                    // off-AIR PI-match loop double-checks against the
                    // runtime Event encoding.
                    let topic_bytes = *blake3::hash(&event.topic).as_bytes();
                    let mut payload_hasher = blake3::Hasher::new();
                    for d in &event.data {
                        payload_hasher.update(d);
                    }
                    let payload_bytes = *payload_hasher.finalize().as_bytes();

                    fn bytes32_to_8_felts(b: &[u8; 32]) -> [BabyBear; 8] {
                        let mut out = [BabyBear::ZERO; 8];
                        for i in 0..8 {
                            let off = i * 4;
                            let v =
                                u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]);
                            // Reduce mod p so we always land in canonical BabyBear.
                            out[i] = BabyBear::new(v % dregg_circuit::field::BABYBEAR_P);
                        }
                        out
                    }

                    vm_effects.push(VmEffect::EmitEvent {
                        topic_hash: bytes32_to_8_felts(&topic_bytes),
                        payload_hash: bytes32_to_8_felts(&payload_bytes),
                    });
                }
                Effect::SpawnWithDelegation {
                    child_public_key,
                    child_token_id,
                    max_staleness,
                } => {
                    // Stage 3: real AIR coverage. Passthrough — the
                    // child cell is its own entity; actor's state
                    // doesn't change.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(child_public_key);
                    hasher.update(child_token_id);
                    hasher.update(&max_staleness.to_le_bytes());
                    let spawn_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::SpawnWithDelegation {
                        spawn_hash: hash_to_8(spawn_hash_bytes.as_bytes()),
                    });
                }
                Effect::RefreshDelegation => {
                    // Stage 3: real AIR coverage. No params on the
                    // runtime side; selector alone records intent.
                    vm_effects.push(VmEffect::RefreshDelegation);
                }
                Effect::RevokeDelegation { child } => {
                    // Stage 3: real AIR coverage. child_hash binds the
                    // target cell into effects_hash.
                    vm_effects.push(VmEffect::RevokeDelegation {
                        child_hash: hash_to_8(child.as_bytes()),
                    });
                }
                Effect::IncrementNonce { cell } if cell == cell_id => {
                    vm_effects.push(VmEffect::IncrementNonce);
                }
                Effect::BridgeMint { portable_proof } => {
                    // Stage 3: real AIR coverage. Balance credit by the
                    // proof's value field. mint_hash binds the proof's
                    // public-input shape (nullifier, root, dest fed,
                    // asset_type) so the prover commits to which bridge
                    // mint event was processed.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(&portable_proof.nullifier);
                    // AttestedRoot is structured; serialize it for hashing.
                    let root_bytes =
                        postcard::to_allocvec(&portable_proof.source_root).unwrap_or_default();
                    hasher.update(&root_bytes);
                    hasher.update(&portable_proof.destination_federation);
                    hasher.update(&portable_proof.asset_type.to_le_bytes());
                    let mint_hash_bytes = hasher.finalize();
                    let value_lo = dregg_circuit::field::BabyBear::new(
                        (portable_proof.value & ((1u64 << 30) - 1)) as u32,
                    );
                    vm_effects.push(VmEffect::BridgeMint {
                        value_lo,
                        mint_hash: hash_to_bb(mint_hash_bytes.as_bytes()),
                        // 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md
                        // §6.5): carry the full u64 in the VmEffect so
                        // the AIR's effects-hash + PI limbs bind to
                        // the entire value, not just the low 30 bits.
                        value_full: portable_proof.value,
                    });
                }

                Effect::Introduce {
                    introducer,
                    recipient,
                    target,
                    permissions,
                } => {
                    // Stage 3: real AIR coverage. Passthrough from the
                    // introducer's POV; recipient-side cap_root update
                    // happens when this turn is replayed against the
                    // recipient cell (separate projection).
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(introducer.as_bytes());
                    hasher.update(recipient.as_bytes());
                    hasher.update(target.as_bytes());
                    let perm_byte: u8 = match permissions {
                        dregg_cell::AuthRequired::None => 0,
                        dregg_cell::AuthRequired::Signature => 1,
                        dregg_cell::AuthRequired::Proof => 2,
                        dregg_cell::AuthRequired::Either => 3,
                        dregg_cell::AuthRequired::Impossible => 4,
                        dregg_cell::AuthRequired::Custom { .. } => 5,
                    };
                    hasher.update(&[perm_byte]);
                    // For Custom, also hash the vk_hash so distinct
                    // Custom modes route to distinct intro hashes.
                    if let dregg_cell::AuthRequired::Custom { vk_hash } = permissions {
                        hasher.update(vk_hash);
                    }
                    let intro_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::Introduce {
                        intro_hash: hash_to_8(intro_hash_bytes.as_bytes()),
                    });
                }
                Effect::PipelinedSend { target, action } => {
                    // Stage 3: real AIR coverage. The dispatching cell
                    // doesn't change state; bind the deferred
                    // dispatch into effects_hash.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(&target.source_turn);
                    hasher.update(&target.output_slot.to_le_bytes());
                    hasher.update(&action.hash());
                    let send_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::PipelinedSend {
                        send_hash: hash_to_8(send_hash_bytes.as_bytes()),
                    });
                }

                Effect::ExerciseViaCapability {
                    cap_slot,
                    inner_effects,
                } => {
                    // Stage 3: real AIR coverage. From the actor's POV
                    // this is passthrough — the inner_effects act on
                    // the target cell. Bind (cap_slot, inner_effects)
                    // via effects_hash so the prover can't swap them.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(&cap_slot.to_le_bytes());
                    for inner in inner_effects {
                        hasher.update(&inner.hash());
                    }
                    let exercise_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::ExerciseViaCapability {
                        exercise_hash: hash_to_8(exercise_hash_bytes.as_bytes()),
                    });
                }

                // ────────────────────────────────────────────────────
                // Stage 7 / P1.A: CapTP runtime effect projections.
                // Each runtime variant maps to its AIR counterpart
                // (selectors 14..17). The AIR params are bound into
                // effects_hash via `compute_effects_hash`, so the
                // prover commits to the specific CapTP operation.
                // The richer Merkle-proof witnesses required to make
                // the AIR non-tautological are added in P1.C.
                // ────────────────────────────────────────────────────

                // ────────────────────────────────────────────────────
                // Near-miss aliasing closure (#100 follow-up): three
                // runtime variants whose VM-side AIR coverage previously
                // either fell through to `_` (no projection) or aliased
                // to a sibling VmEffect (Transfer-dir-1 / SetPermissions /
                // RevokeCapability). Each now projects to a dedicated
                // VmEffect whose AIR constraints are algebraically
                // distinct from the sibling — see the matching variant
                // arms in `circuit/src/effect_vm/air.rs`.
                // ────────────────────────────────────────────────────
                Effect::Burn {
                    target,
                    slot: _,
                    amount,
                } if target == cell_id => {
                    use dregg_circuit::field::BabyBear;
                    let target_hash = hash_to_bb(target.as_bytes());
                    // Low 30 bits drive the AIR balance debit; the full
                    // u64 is bound through `compute_effects_hash`.
                    let amount_lo = BabyBear::new((*amount & ((1u64 << 30) - 1)) as u32);
                    vm_effects.push(VmEffect::Burn {
                        target_hash,
                        amount_lo,
                        amount_full: *amount,
                    });
                }
                Effect::CellDestroy {
                    target,
                    certificate,
                } if target == cell_id => {
                    let target_hash = hash_to_8(target.as_bytes());
                    let cert_hash = certificate.certificate_hash();
                    vm_effects.push(VmEffect::CellDestroy {
                        target_hash,
                        death_certificate_hash: hash_to_8(&cert_hash),
                    });
                }
                Effect::AttenuateCapability {
                    cell,
                    slot,
                    narrower_permissions,
                    narrower_effects,
                    narrower_expiry,
                } if cell == cell_id => {
                    // Bind the slot identifier (low 4 bytes of its LE
                    // encoding) into the first param, and a commitment
                    // over (permissions, effect_mask, expiry) into the
                    // second. The narrower_commitment is the canonical
                    // BLAKE3 over the same byte stream the runtime's
                    // journal entry / receipt-hash will absorb, so a
                    // forged "wider" attenuation cannot collide.
                    let slot_bytes = slot.to_le_bytes();
                    let cap_slot_hash = hash_to_8(blake3::hash(&slot_bytes).as_bytes());
                    let mut h = blake3::Hasher::new();
                    h.update(b"DREGG_ATTN_NARROWER/v1");
                    let perm_bytes =
                        postcard::to_allocvec(narrower_permissions).unwrap_or_default();
                    h.update(&perm_bytes);
                    if let Some(mask) = narrower_effects {
                        h.update(&[1u8]);
                        h.update(&mask.to_le_bytes());
                    } else {
                        h.update(&[0u8]);
                    }
                    if let Some(exp) = narrower_expiry {
                        h.update(&[1u8]);
                        h.update(&exp.to_le_bytes());
                    } else {
                        h.update(&[0u8]);
                    }
                    let narrower_commitment = hash_to_8(h.finalize().as_bytes());
                    vm_effects.push(VmEffect::AttenuateCapability {
                        cap_slot_hash,
                        narrower_commitment,
                        // The runtime→VM bridge keeps the legacy opaque projection
                        // (no in-circuit Phase-B non-amp witness here); the
                        // executor enforces narrowing off-circuit. A Phase-B
                        // witnessed projection is a follow-up bridge change.
                        phase_b: None,
                    });
                }

                // ────────────────────────────────────────────────────
                // AIR-impl lane (#119): four runtime variants that
                // previously fell through to `_ => {}` (NoOp shim).
                // Each now projects to a dedicated VmEffect with its
                // own selector + AIR constraint set.
                // ────────────────────────────────────────────────────
                Effect::CellSeal { target, reason } if target == cell_id => {
                    let target_hash = hash_to_8(target.as_bytes());
                    // `reason` is a 32-byte commitment to the sealing
                    // rationale; we project all 32 bytes into 8 limbs.
                    let reason_hash = hash_to_8(reason);
                    vm_effects.push(VmEffect::CellSeal {
                        target: target_hash,
                        reason_hash,
                    });
                }
                Effect::CellUnseal { target } if target == cell_id => {
                    let target_hash = hash_to_8(target.as_bytes());
                    vm_effects.push(VmEffect::CellUnseal {
                        target: target_hash,
                    });
                }
                Effect::ReceiptArchive {
                    prefix_end_height,
                    checkpoint,
                } if checkpoint.cell_id == *cell_id => {
                    use dregg_circuit::field::BabyBear;
                    let target_hash = hash_to_8(checkpoint.cell_id.as_bytes());
                    // Low-30-bit truncation of the end height for the AIR
                    // balance-arithmetic shape; consistent with how other
                    // u64-height fields are projected in this bridge.
                    let end_height_bb =
                        BabyBear::new((*prefix_end_height & ((1u64 << 30) - 1)) as u32);
                    let terminal_hash = hash_to_8(&checkpoint.archive_terminal_receipt_hash);
                    vm_effects.push(VmEffect::ReceiptArchive {
                        target: target_hash,
                        archive_end_height: end_height_bb,
                        terminal_receipt_hash: terminal_hash,
                    });
                }
                Effect::Refusal {
                    cell,
                    offered_action_commitment,
                    refusal_reason,
                    proof_witness_index: _,
                } if cell == cell_id => {
                    let target_hash = hash_to_8(cell.as_bytes());
                    // Encode `reason_hash` over the FULL 32-byte commitment plus
                    // the reason discriminant: XOR the discriminant into the low
                    // 4 bytes of the commitment, then project all 32 bytes into
                    // 8 limbs. This binds the entire (reason, commitment) pair
                    // at ~256-bit strength (was a single ~31-bit fold). See the
                    // shared `refusal_reason_bytes` helper for the canonical
                    // encoding — both projectors call it so they agree
                    // byte-for-byte.
                    let discriminant = match refusal_reason {
                        crate::action::RefusalReason::Declined => 0u32,
                        crate::action::RefusalReason::NoAuthority => 1u32,
                        crate::action::RefusalReason::WindowExpired => 2u32,
                        crate::action::RefusalReason::Custom { .. } => 3u32,
                    };
                    let reason_bytes = dregg_circuit::effect_vm::refusal_reason_bytes(
                        offered_action_commitment,
                        discriminant,
                    );
                    let reason_hash = hash_to_8(&reason_bytes);
                    vm_effects.push(VmEffect::Refusal {
                        target: target_hash,
                        reason_hash,
                    });
                }

                _ => {
                    // Effects not targeting `cell_id` or arms covered by
                    // explicit guards above (e.g., a cross-cell effect
                    // whose other end isn't us) are silently skipped —
                    // they're not part of this cell's proof.
                }
            }
        }
        for child in &tree.children {
            collect_effects(child, cell_id, vm_effects);
        }
    }

    // Stage 3 complete: push_pending_shim was the temporary scaffolding
    // for the 22 variants without dedicated AIR coverage. All 22 now
    // have real per-variant AIR variants, so the shim is removed.
    // The `effect-vm-pending-shim` feature flag is no longer used.

    let mut vm_effects = Vec::new();
    for root in &turn.call_forest.roots {
        collect_effects(root, cell_id, &mut vm_effects);
    }

    // Must have at least one effect for the VM.
    if vm_effects.is_empty() {
        vm_effects.push(dregg_circuit::effect_vm::Effect::NoOp);
    }
    vm_effects
}
