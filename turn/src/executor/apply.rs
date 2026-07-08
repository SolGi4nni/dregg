//! Effect application: per-`Effect` `apply_*` methods plus a thin dispatcher.
//!
//! Originally extracted from `executor/mod.rs` (lines 6150-9565 of pre-decomposition
//! file) as a single 3400-LOC `match effect` block. Decomposed into per-variant
//! methods so each effect's apply logic can be tested independently — every
//! `apply_<variant>` is a regular method on `TurnExecutor` and may be called
//! directly with a hand-built `Ledger` + `LedgerJournal`.
//!
//! Behavior is unchanged: each `apply_<variant>` is a verbatim move of the
//! corresponding old match arm, and `apply_effect` is reduced to a dispatcher.

use super::*;
use dregg_cell::*;
use dregg_cell_crypto::PortableNoteProof;

/// Domain-separate a shielded transfer's BabyBear field nullifier into a 32-byte
/// `note_nullifiers` set key. The shielded nullifier is a field element (the
/// chain's double-spend tag for that hidden input); hashing it under a dedicated
/// derive-key keeps shielded nullifiers in a disjoint namespace from cleartext
/// note nullifiers while preserving injectivity for distinct field elements.
///
/// Only the `prover`-enabled executor admits shielded transfers (the hiding
/// uni-STARK verifier lives in `dregg-circuit-prove`), so this key derivation is
/// scoped to that build; a verify-only executor fails the effect closed instead.
#[cfg(feature = "prover")]
fn shielded_nullifier_key(field_nullifier: u32) -> Nullifier {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-shielded-nullifier v1");
    hasher.update(&field_nullifier.to_le_bytes());
    Nullifier(*hasher.finalize().as_bytes())
}

/// Verify a note-spend leaf proof (BridgeMint) against the IR-v2 descriptor
/// prover — the consumer half of the `StarkProof` → `Ir2BatchProof` wire flip
/// (stark-kill). This is the leaf leg `apply_bridge_mint`'s `verify_stark`
/// closure delegates to after compressing the byte-domain bridge material to
/// the six source felts.
///
/// `proof_bytes` is a `postcard`-encoded
/// [`dregg_circuit::descriptor_ir2::Ir2BatchProof`] (the NEW wire format, NOT
/// the legacy hand-STARK blob). The descriptor is fetched FAIL-CLOSED by name
/// (`note-spend-leaf::dregg-note-spending-dsl-v3`); an unregistered name rejects
/// rather than falling back to any legacy path. The 7-slot claim tuple is
/// `[nullifier, merkle_root, value_lo, asset_type, destination_federation,
/// value_hi, mint_hash]` — the same six compressed felts the retired
/// `verify_note_spend_dsl_full` bound, plus the appended felt-domain mint
/// identity ([`note_spend_mint_hash_felt`]) that the note-spend AIR recomputes
/// in-circuit and pins to `pi[6]`. The boundary pins over
/// {NULLIFIER, VALUE, VALUE_HI, ASSET_TYPE, DESTINATION_FEDERATION}, the
/// last-row Merkle-root pin, and the `MINT_HASH` pin make every one of those
/// slots a cryptographic binding, so the four bridge trapdoors
/// (cross-federation replay, value inflation, asset-type confusion,
/// recipient substitution) stay closed.
///
/// [`note_spend_mint_hash_felt`]: dregg_circuit::dsl::note_spending::note_spend_mint_hash_felt
#[allow(clippy::too_many_arguments)]
fn verify_note_spend_descriptor2(
    nullifier: dregg_circuit::BabyBear,
    merkle_root: dregg_circuit::BabyBear,
    value_lo: dregg_circuit::BabyBear,
    value_hi: dregg_circuit::BabyBear,
    asset_type: dregg_circuit::BabyBear,
    destination_federation: dregg_circuit::BabyBear,
    proof_bytes: &[u8],
) -> Result<(), String> {
    use dregg_circuit::descriptor_by_name::descriptor_by_name;
    use dregg_circuit::descriptor_ir2::{DreggStarkConfig, Ir2BatchProof, verify_vm_descriptor2};
    use dregg_circuit::dsl::note_spending::note_spend_mint_hash_felt;
    use dregg_circuit::note_spend_witness::NOTE_SPEND_LEAF_NAME;

    // 1. Fail-closed descriptor dispatch by name.
    let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).ok_or_else(|| {
        format!("note-spend leaf descriptor `{NOTE_SPEND_LEAF_NAME}` is not registered")
    })?;

    // 2. Decode the NEW wire format: postcard(Ir2BatchProof).
    let batch: Ir2BatchProof<DreggStarkConfig> = postcard::from_bytes(proof_bytes)
        .map_err(|e| format!("note-spend BatchProof postcard decode failed: {e}"))?;

    // 3. Rebuild the 7-slot claim tuple in descriptor PI order and check it.
    //    (nullifier, merkle_root, value_lo, asset_type, destination_federation,
    //    value_hi) are pi[0..6]; the felt-domain mint identity is pi[6].
    let mint = note_spend_mint_hash_felt(
        nullifier,
        merkle_root,
        value_lo,
        asset_type,
        destination_federation,
        value_hi,
    );
    let pi = vec![
        nullifier,
        merkle_root,
        value_lo,
        asset_type,
        destination_federation,
        value_hi,
        mint,
    ];

    verify_vm_descriptor2(&desc, &batch, &pi)
        .map_err(|e| format!("note-spend descriptor verification failed: {e}"))
}

impl TurnExecutor {
    /// Apply a single effect to the ledger, recording undo entries in the journal.
    ///
    /// SECURITY: For any effect that names a cell other than `action_target`,
    /// we verify that the actor holds a capability to that cell AND that the
    /// relevant permission on that cell allows the operation.
    /// TRUST-CRITICAL: This function directly mutates ledger state (balances, fields, cells).
    /// If compromised: balance inflation/deflation, unauthorized state overwrites, or
    /// cell creation without proper authorization. All mutations are journaled for rollback.
    /// Future: replace with verified effect application via Effect VM STARK proof for all
    /// effect types (currently only sovereign cells use proof-carrying effects).
    pub(crate) fn apply_effect(
        &self,
        effect: &Effect,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        match effect {
            Effect::SetField { cell, index, value } => self.apply_set_field(
                ledger,
                path,
                action_target,
                actor,
                journal,
                cell,
                *index,
                value,
            ),
            Effect::Transfer { from, to, amount } => self.apply_transfer(
                ledger,
                path,
                action_target,
                actor,
                journal,
                from,
                to,
                *amount,
            ),
            Effect::GrantCapability { from, to, cap } => self.apply_grant_capability(
                ledger,
                path,
                action_target,
                actor,
                journal,
                from,
                to,
                cap,
            ),
            Effect::RevokeCapability { cell, slot } => self.apply_revoke_capability(
                ledger,
                path,
                action_target,
                actor,
                journal,
                cell,
                *slot,
            ),
            Effect::EmitEvent { cell, event } => {
                self.apply_emit_event(ledger, path, journal, cell, event)
            }
            Effect::IncrementNonce { cell } => {
                self.apply_increment_nonce(ledger, path, action_target, actor, journal, cell)
            }
            Effect::CreateCell {
                public_key,
                token_id,
                balance,
            } => self.apply_create_cell(ledger, path, journal, public_key, token_id, *balance),
            Effect::SetPermissions {
                cell,
                new_permissions,
            } => self.apply_set_permissions(
                ledger,
                path,
                action_target,
                actor,
                journal,
                cell,
                new_permissions,
            ),
            Effect::SetVerificationKey { cell, new_vk } => self.apply_set_verification_key(
                ledger,
                path,
                action_target,
                actor,
                journal,
                cell,
                new_vk.as_ref(),
            ),
            Effect::SetProgram { cell, program } => {
                self.apply_set_program(ledger, path, action_target, actor, journal, cell, program)
            }
            Effect::NoteSpend {
                nullifier,
                note_tree_root,
                spending_proof,
                value,
                asset_type,
                value_commitment,
            } => self.apply_note_spend(
                path,
                journal,
                nullifier,
                note_tree_root,
                spending_proof,
                *value,
                *asset_type,
                value_commitment.as_ref(),
            ),
            Effect::NoteCreate {
                commitment,
                value_commitment,
                range_proof,
                ..
            } => self.apply_note_create(
                path,
                journal,
                commitment,
                value_commitment.as_ref(),
                range_proof.as_deref(),
            ),
            Effect::BridgeMint { portable_proof } => {
                self.apply_bridge_mint(path, journal, portable_proof)
            }

            Effect::ExerciseViaCapability {
                cap_slot,
                inner_effects,
            } => self.apply_exercise_via_capability(
                ledger,
                path,
                actor,
                journal,
                *cap_slot,
                inner_effects,
            ),
            Effect::PipelinedSend { target, .. } => self.apply_pipelined_send(path, target),

            Effect::Introduce {
                introducer,
                recipient,
                target,
                permissions,
            } => self.apply_introduce(
                ledger,
                path,
                journal,
                introducer,
                recipient,
                target,
                permissions,
            ),

            Effect::SpawnWithDelegation {
                child_public_key,
                child_token_id,
                max_staleness,
            } => self.apply_spawn_with_delegation(
                ledger,
                path,
                action_target,
                journal,
                child_public_key,
                child_token_id,
                *max_staleness,
            ),
            Effect::RefreshDelegation { child, snapshot } => {
                self.apply_refresh_delegation(ledger, path, action_target, journal, child, snapshot)
            }
            Effect::RevokeDelegation { child } => {
                self.apply_revoke_delegation(ledger, path, action_target, journal, child)
            }
            Effect::MakeSovereign { cell } => {
                self.apply_make_sovereign(ledger, path, action_target, cell)
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                owner_pubkey,
                token_id,
                params,
            } => self.apply_create_cell_from_factory(
                ledger,
                path,
                journal,
                factory_vk,
                owner_pubkey,
                token_id,
                params,
            ),

            Effect::Refusal {
                cell,
                offered_action_commitment,
                refusal_reason,
                proof_witness_index,
            } => self.apply_refusal(
                ledger,
                path,
                action_target,
                actor,
                journal,
                cell,
                offered_action_commitment,
                refusal_reason,
                *proof_witness_index,
            ),
            Effect::CellSeal { target, reason } => {
                self.apply_cell_seal(ledger, path, action_target, journal, target, *reason)
            }
            Effect::CellUnseal { target } => {
                self.apply_cell_unseal(ledger, path, action_target, journal, target)
            }
            Effect::CellDestroy {
                target,
                certificate,
            } => self.apply_cell_destroy(ledger, path, action_target, journal, target, certificate),
            Effect::Burn {
                target,
                slot,
                amount,
            } => self.apply_burn(
                ledger,
                path,
                action_target,
                actor,
                journal,
                target,
                *slot,
                *amount,
            ),
            Effect::Mint {
                target,
                slot,
                amount,
            } => self.apply_mint(ledger, path, actor, journal, target, *slot, *amount),
            Effect::AttenuateCapability {
                cell,
                slot,
                narrower_permissions,
                narrower_effects,
                narrower_expiry,
            } => self.apply_attenuate_capability(
                ledger,
                path,
                actor,
                journal,
                cell,
                *slot,
                narrower_permissions,
                *narrower_effects,
                *narrower_expiry,
            ),
            Effect::ReceiptArchive {
                prefix_end_height,
                checkpoint,
            } => self.apply_receipt_archive(
                ledger,
                path,
                action_target,
                journal,
                *prefix_end_height,
                checkpoint,
            ),
            Effect::Promise {
                cell,
                resolution_condition,
                wake,
                timeout_height,
            } => self.apply_promise(
                path,
                actor,
                cell,
                resolution_condition,
                wake,
                *timeout_height,
            ),
            Effect::Notify {
                from,
                to,
                wake,
                resolution_condition,
                timeout_height,
            } => self.apply_notify(
                path,
                actor,
                from,
                to,
                wake,
                resolution_condition,
                *timeout_height,
            ),
            Effect::React {
                pending_id,
                condition,
                resolution_proof,
                wake,
            } => self.apply_react(path, journal, pending_id, condition, resolution_proof, wake),
            Effect::ShieldedTransfer { payload } => {
                self.apply_shielded_transfer(path, journal, payload)
            }
        }
    }

    // ─── Per-Effect apply methods ────────────────────────────────────────────
    //
    // Each method below is the verbatim body of the corresponding match arm
    // from the pre-decomposition `apply_effect`. The signatures pass through
    // exactly the variant fields plus the ambient ledger/path/journal/actor
    // context. Behavior is unchanged.

    fn apply_set_field(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        index: usize,
        value: &FieldElement,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetState,
                "SetState",
                dregg_cell::EFFECT_SET_FIELD,
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        // KERNEL ALIGNMENT (lifecycle liveness): the verified `stateStep`
        // (`Dregg2.Exec.EffectsState.lean:208`) gates the field write on
        // `cellLive target` (Live-ONLY). A write into a Sealed/Destroyed cell
        // returns `none` in Lean (`state_nonlive_fails`); mirror that here.
        if !c.is_live() {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!("SetField target cell {cell} is not live (sealed/destroyed)"),
                },
                path.to_vec(),
            ));
        }
        if index < STATE_SLOTS {
            // Fixed register-file slot: the legacy 16-slot path.
            journal.record_set_field(*cell, index, Some(c.state.fields[index]));
            c.state.fields[index] = *value;
            // Invalidate stale field commitment (the old hash no longer matches).
            if c.state.commitments[index].is_some() {
                c.state.commitments[index] = None;
            }
        } else {
            // Heap field (key >= STATE_SLOTS): the openable sorted-map spine.
            // The journal stores the slot as usize; umem.rs reads it back as u64.
            let old_value = c.state.get_field_ext(index as u64);
            journal.record_set_field(*cell, index, old_value);
            c.state.set_field_ext(index as u64, *value);
        }
        Ok(())
    }

    fn apply_transfer(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        from: &CellId,
        to: &CellId,
        amount: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // KERNEL ALIGNMENT: the verified kernel REJECTS a self-transfer
        // (`Dregg2.Exec.RecordKernel.recKExecAsset` requires `src ≠ dst`,
        // returning `none`). Without this guard Rust commits a self-move as a
        // balance no-op that still charges fee + ticks nonce + emits a receipt —
        // a turn Lean rolls back, i.e. a rejection-parity asymmetry (Rust accepts
        // what the verified kernel refuses).
        if from == to {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!("self-transfer rejected: src == dst ({from})"),
                },
                path.to_vec(),
            ));
        }
        if from != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                from,
                dregg_cell::permissions::Action::Send,
                "Send",
                dregg_cell::EFFECT_TRANSFER,
                path,
            )?;
        }
        // Transfer is an ORDINARY move (signed-balance discipline, THE EPOCH
        // §5): the source may not go below zero; the destination credit is
        // overflow-checked.
        let from_cell = ledger
            .get(from)
            .ok_or_else(|| (TurnError::CellNotFound { id: *from }, path.to_vec()))?;
        // KERNEL ALIGNMENT (lifecycle liveness): the verified kernel's asset
        // move gates BOTH legs on Live-ONLY. The SOURCE is gated by
        // `recKExecAsset` (`cellLifecycleLive k turn.src`,
        // `Dregg2.Exec.RecordKernel.lean:613`); the DEST by `recCexecAsset`
        // (`acceptsEffects s.kernel t.dst`, `TurnExecutorFull.lean:893`). Both
        // Lean predicates are Live-ONLY (discriminant `0`), so a Sealed /
        // Destroyed / Archived endpoint refuses the move. Without these guards
        // a live agent could transfer FROM or credit INTO a sealed/destroyed
        // cell that Lean rolls back.
        if !from_cell.is_live() {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!("Transfer source cell {from} is not live (sealed/destroyed)"),
                },
                path.to_vec(),
            ));
        }
        let amount_i = i64::try_from(amount)
            .map_err(|_| (TurnError::BalanceOverflow { cell: *from }, path.to_vec()))?;
        if from_cell.state.balance() < amount_i {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *from,
                    required: amount,
                    available: from_cell.state.balance(),
                },
                path.to_vec(),
            ));
        }
        let to_cell = ledger
            .get(to)
            .ok_or_else(|| (TurnError::TransferDestNotFound { id: *to }, path.to_vec()))?;
        if !to_cell.is_live() {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "Transfer destination cell {to} is not live (sealed/destroyed)"
                    ),
                },
                path.to_vec(),
            ));
        }
        let to_balance = ledger.get(to).unwrap().state.balance();
        if to_balance.checked_add(amount_i).is_none() {
            return Err((TurnError::BalanceOverflow { cell: *to }, path.to_vec()));
        }
        // Record old balances, then apply.
        let old_from_balance = ledger.get(from).unwrap().state.balance();
        let old_to_balance = ledger.get(to).unwrap().state.balance();
        journal.record_set_balance(*from, old_from_balance);
        journal.record_set_balance(*to, old_to_balance);
        ledger
            .get_mut(from)
            .unwrap()
            .state
            .set_balance(old_from_balance - amount_i);
        ledger
            .get_mut(to)
            .unwrap()
            .state
            .set_balance(old_to_balance + amount_i);
        Ok(())
    }

    fn apply_grant_capability(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        from: &CellId,
        to: &CellId,
        cap: &CapabilityRef,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if from != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                from,
                dregg_cell::permissions::Action::Delegate,
                "Delegate",
                dregg_cell::EFFECT_GRANT_CAPABILITY,
                path,
            )?;
        }

        let from_cell = ledger
            .get(from)
            .ok_or_else(|| (TurnError::CellNotFound { id: *from }, path.to_vec()))?;

        // A cell implicitly holds the strongest capability over itself:
        // granting access to its own cell is authorized by the signed
        // action (the cell's owner consents). For cross-cell grants the
        // granter must hold an explicit c-list entry pointing at the
        // target.
        if cap.target == *from {
            // Self-grant: skip c-list lookup; the signature on the
            // action proves the cell owner consents to share access
            // to their own cell. Attenuation against an implicit
            // self-cap is always satisfied (the implicit cap is the
            // strongest possible ON EVERY AXIS: permissions ⊤, mask
            // EFFECT_ALL, expiry unbounded) — any requested mask/expiry
            // is an attenuation of it.
        } else {
            let held_cap = from_cell
                .capabilities
                .lookup_by_target(&cap.target)
                .ok_or_else(|| {
                    (
                        TurnError::CapabilityNotHeld {
                            actor: *from,
                            target: cap.target,
                        },
                        path.to_vec(),
                    )
                })?;

            // B2 non-amp, axis 1 — AuthRequired lattice: granted ⊑ held.
            if !dregg_cell::is_attenuation(&held_cap.permissions, &cap.permissions) {
                return Err((
                    TurnError::DelegationDenied {
                        parent: *from,
                        child_target: *to,
                    },
                    path.to_vec(),
                ));
            }

            // B2 non-amp, axis 2 — facet SUBMASK: the granted effect mask
            // must be a bitwise subset of the held mask (`None` = EFFECT_ALL,
            // matching the circuit's Phase-B2 leaf encoding in
            // `cap_ref_to_leaf`). Previously unchecked: a holder of a
            // TRANSFER-only facet could grant an all-effects cap.
            let held_mask = held_cap.allowed_effects.unwrap_or(EFFECT_ALL);
            let granted_mask = cap.allowed_effects.unwrap_or(EFFECT_ALL);
            if !is_facet_attenuation(held_mask, granted_mask) {
                return Err((
                    TurnError::DelegationDenied {
                        parent: *from,
                        child_target: *to,
                    },
                    path.to_vec(),
                ));
            }

            // B2 non-amp, axis 3 — EXPIRY-MONOTONE: granted ⊑ held over the
            // expiry lattice (`None` = ⊤ unbounded; finite shrink-only,
            // matching the circuit's monotone-expiry GTE gate). A holder of
            // a height-bounded cap must not grant an unbounded (or
            // later-expiring) one.
            if let Some(held_exp) = held_cap.expires_at {
                match cap.expires_at {
                    None => {
                        return Err((
                            TurnError::DelegationDenied {
                                parent: *from,
                                child_target: *to,
                            },
                            path.to_vec(),
                        ));
                    }
                    Some(granted_exp) if granted_exp > held_exp => {
                        return Err((
                            TurnError::DelegationDenied {
                                parent: *from,
                                child_target: *to,
                            },
                            path.to_vec(),
                        ));
                    }
                    Some(_) => {}
                }
            }
        }

        let to_cell = ledger
            .get_mut(to)
            .ok_or_else(|| (TurnError::CellNotFound { id: *to }, path.to_vec()))?;
        // B2: install the entry FAITHFULLY — carrying the granted
        // `allowed_effects` + `expires_at` (+ breadstuff + R7 stored_epoch)
        // just gated above. The old install path
        // (`grant_with_breadstuff`) silently widened every grant to
        // `allowed_effects: None, expires_at: None` — amplifying on the mask
        // and expiry axes at install time even when the wire grant was
        // properly attenuated. The circuit (Phase B2) already enforces the
        // submask + lattice + expiry-monotone semantics; this makes the
        // executor MATCH it.
        let granted_slot = to_cell.capabilities.grant_ref(cap).ok_or_else(|| {
            (
                TurnError::CapabilitySlotOverflow { cell: *to },
                path.to_vec(),
            )
        })?;
        journal.record_grant_capability(*to, granted_slot);
        Ok(())
    }

    fn apply_revoke_capability(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        slot: u32,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::Delegate,
                "Delegate",
                dregg_cell::EFFECT_REVOKE_CAPABILITY,
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        if let Some(old_cap) = c.capabilities.lookup(slot).cloned() {
            journal.record_revoke_capability(*cell, old_cap);
        }
        c.capabilities.revoke(slot);
        Ok(())
    }

    fn apply_emit_event(
        &self,
        ledger: &Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        cell: &CellId,
        event: &Event,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let emit_cell = ledger
            .get(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        // KERNEL ALIGNMENT — §LIVENESS-GATE (CLASS-1): the verified kernel's
        // emit arm (`emitEventA`, TurnExecutorFull.lean:2529) admits an event
        // ONLY when the target cell is a member AND its lifecycle still
        // `acceptsEffects` — a Sealed/Destroyed/Migrated cell CANNOT post an
        // observation ("Destroyed is terminal"). Membership alone (the prior
        // `ledger.get(cell).is_none()`) let a non-accepting cell emit, where the
        // verified kernel refuses. (Authority is deliberately NOT gated here —
        // Lean's emit arm has no authority leg either; only the liveness leg is
        // added.) Fail-closed on a non-accepting lifecycle.
        if !emit_cell.accepts_effects() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "EmitEvent target cell does not accept effects (sealed/destroyed)"
                        .into(),
                },
                path.to_vec(),
            ));
        }
        // Record the event in the journal so it appears in the turn receipt.
        journal.record_event_emitted(*cell, event.topic, event.data.clone());
        Ok(())
    }

    fn apply_increment_nonce(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::IncrementNonce,
                "IncrementNonce",
                dregg_cell::EFFECT_INCREMENT_NONCE,
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        // KERNEL ALIGNMENT (lifecycle liveness): `incrementNonceA` routes
        // through `incrementNonceStep` → the bare authority-gated `stateStep`
        // (`Dregg2.Exec.EffectsState.lean:208`), which gates `cellLive target`
        // (Live-ONLY). A nonce bump on a Sealed/Destroyed cell returns `none`.
        if !c.is_live() {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "IncrementNonce target cell {cell} is not live (sealed/destroyed)"
                    ),
                },
                path.to_vec(),
            ));
        }
        journal.record_set_nonce(*cell, c.state.nonce());
        if !c.state.increment_nonce() {
            return Err((TurnError::NonceOverflow { cell: *cell }, path.to_vec()));
        }
        Ok(())
    }

    fn apply_create_cell(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        public_key: &[u8; 32],
        token_id: &[u8; 32],
        balance: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if balance != 0 {
            return Err((
                TurnError::CreateCellNonZeroBalance {
                    cell: CellId::derive_raw(public_key, token_id),
                    balance,
                },
                path.to_vec(),
            ));
        }
        let new_cell = Cell::with_balance(*public_key, *token_id, 0);
        let id = new_cell.id();
        ledger
            .insert_cell(new_cell)
            .map_err(|_| (TurnError::CellAlreadyExists { id }, path.to_vec()))?;
        journal.record_create_cell(id);
        Ok(())
    }

    fn apply_set_permissions(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        new_permissions: &dregg_cell::Permissions,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetPermissions,
                "SetPermissions",
                dregg_cell::EFFECT_SET_PERMISSIONS,
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        // KERNEL ALIGNMENT (lifecycle liveness): `setPermissionsA` routes to the
        // bare authority-gated `stateStep` (`Dregg2.Exec.EffectsState.lean:208`),
        // gating `cellLive target` (Live-ONLY). A permissions write into a
        // Sealed/Destroyed cell returns `none`.
        if !c.is_live() {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "SetPermissions target cell {cell} is not live (sealed/destroyed)"
                    ),
                },
                path.to_vec(),
            ));
        }
        journal.record_set_permissions(*cell, c.permissions.clone());
        c.permissions = new_permissions.clone();
        Ok(())
    }

    fn apply_set_verification_key(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        new_vk: Option<&dregg_cell::VerificationKey>,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetVerificationKey,
                "SetVerificationKey",
                dregg_cell::EFFECT_SET_VERIFICATION_KEY,
                path,
            )?;
        }
        // Audit P0 #69: the apply path must reject `VerificationKey`s
        // whose declared `hash` is not `blake3(data)`. Without this
        // check a turn can pin an arbitrary `hash` while shipping
        // unrelated `data`, which then propagates into the cell
        // commitment (via `commitment.rs` line 148, `hasher.update(&vk.hash)`)
        // and into downstream verifiers that re-derive program
        // identity from the hash. Reject the apply rather than silently
        // accepting a mis-bound VK.
        if let Some(vk) = new_vk {
            let expected = *blake3::hash(&vk.data).as_bytes();
            if expected != vk.hash {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "SetVerificationKey: VerificationKey integrity invariant violated \
                             (declared hash {:02x}{:02x}.. but blake3(data) is {:02x}{:02x}..)",
                            vk.hash[0], vk.hash[1], expected[0], expected[1],
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        // KERNEL ALIGNMENT (lifecycle liveness): `setVKA` routes to the bare
        // authority-gated `stateStep` (`Dregg2.Exec.EffectsState.lean:208`),
        // gating `cellLive target` (Live-ONLY). A VK write into a
        // Sealed/Destroyed cell returns `none`.
        if !c.is_live() {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "SetVerificationKey target cell {cell} is not live (sealed/destroyed)"
                    ),
                },
                path.to_vec(),
            ));
        }
        journal.record_set_verification_key(*cell, c.verification_key.clone());
        c.verification_key = new_vk.cloned();
        Ok(())
    }

    /// Re-program a cell's [`CellProgram`] (its caveat table) as an ordered
    /// effect — the in-protocol replacement for the out-of-band genesis-path
    /// `set_cell_program` mutation (the persist-durability category error: a
    /// runtime reprogram is an ORDERED turn, not timeless genesis).
    ///
    /// Authority: a SELF-targeted install (the cell re-programming itself) is
    /// authorized by the signed action exactly as `apply_set_verification_key`
    /// is — a cell's program and VK are one program-identity authority surface.
    /// A CROSS-CELL install requires the actor to hold `SetVerificationKey`
    /// permission on the target (the same program-identity gate). Applied LAST
    /// within an action ([`Effect::is_permission_effect`]) so an action cannot
    /// loosen its own caveats and then exploit the loosened gate in a later
    /// effect of the same action.
    ///
    /// CIRCUIT WITNESS (FOLLOW-UP): no descriptor rung binds this write into the
    /// turn commitment yet — that is VK-affecting (ember-gated). The executor
    /// path lands now so the genesis redirect works; the in-circuit witness is
    /// the owed follow-up.
    fn apply_set_program(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        program: &dregg_cell::CellProgram,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetVerificationKey,
                "SetProgram",
                dregg_cell::EFFECT_SET_PROGRAM,
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        // KERNEL ALIGNMENT (lifecycle liveness): `setProgramA` routes to the bare
        // authority-gated `stateStep` (`Dregg2.Exec.EffectsState.lean:208`),
        // gating `cellLive target` (Live-ONLY). A program write into a
        // Sealed/Destroyed cell returns `none`.
        if !c.is_live() {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!("SetProgram target cell {cell} is not live (sealed/destroyed)"),
                },
                path.to_vec(),
            ));
        }
        journal.record_set_program(*cell, c.program.clone());
        c.program = program.clone();
        Ok(())
    }

    fn apply_note_spend(
        &self,
        path: &[usize],
        journal: &mut LedgerJournal,
        nullifier: &Nullifier,
        note_tree_root: &[u8; 32],
        spending_proof: &[u8],
        value: u64,
        asset_type: u64,
        // BUG #115: previously dropped via `..`; now validated and bound.
        // When present, `value_commitment` must be a valid compressed Ristretto
        // point. Binding it here (via journal.record_note_spend_commitment)
        // makes it observable in the turn receipt. Conservation and
        // Schnorr-excess proof are verified at the finalize layer
        // (`check_committed_conservation`).
        value_commitment: Option<&[u8; 32]>,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate nullifier is well-formed (non-zero).
        if nullifier.0.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null nullifier in NoteSpend".into(),
                },
                path.to_vec(),
            ));
        }
        // Validate note_tree_root is non-zero (must reference a real tree state).
        if note_tree_root.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null note_tree_root in NoteSpend".into(),
                },
                path.to_vec(),
            ));
        }
        // Verify the ZK spending proof: proves the spender knows the note's
        // opening, the nullifier is correctly derived, and the note commitment
        // exists in the note tree at the given root.
        if spending_proof.is_empty() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "NoteSpend missing spending proof".into(),
                },
                path.to_vec(),
            ));
        }
        let verifier = self.proof_verifier.as_ref().ok_or_else(|| {
            (
                TurnError::InvalidEffect {
                    reason: "no proof verifier configured for note spend verification".into(),
                },
                path.to_vec(),
            )
        })?;
        // Public inputs for the note spending STARK (advisory buffer for
        // the wire-side verifier; the real PI lives in the embedded proof):
        // nullifier || note_tree_root || value || asset_type || dest_fed
        //
        // SECURITY: value and asset_type are bound via boundary constraints
        // to the actual note preimage columns. A spender cannot claim a
        // different value/asset_type than what is committed in the note —
        // the proof verification will fail. destination_federation is
        // ZERO for local (non-bridge) spends; the AIR boundary pins col 18
        // to pi[4] so a bridge-shaped proof (non-zero dest) cannot be
        // replayed against the local-spend path.
        let mut public_inputs = Vec::with_capacity(112);
        public_inputs.extend_from_slice(&nullifier.0);
        public_inputs.extend_from_slice(note_tree_root);
        public_inputs.extend_from_slice(&value.to_le_bytes());
        public_inputs.extend_from_slice(&asset_type.to_le_bytes());
        // destination_federation = ZERO for local spends.
        public_inputs.extend_from_slice(&[0u8; 32]);
        if !verifier.verify(spending_proof, "note-spend", "note-tree", &public_inputs) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "NoteSpend spending proof verification failed".into(),
                },
                path.to_vec(),
            ));
        }
        // Insert into the production note-nullifier set with double-spend
        // rejection. This is the ledger-side gate that prevents the same
        // nullifier from being re-presented in a later turn. The insert is
        // journaled so a turn that fails *after* this point unwinds the
        // record (preventing a deliberate-failure attack that would
        // permanently burn the note).
        {
            let mut set = self.note_nullifiers.lock().unwrap();
            if set.contains(nullifier) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "double-spend: nullifier already in note_nullifiers set"
                            .to_string(),
                    },
                    path.to_vec(),
                ));
            }
            set.insert(*nullifier).map_err(|e| {
                // `insert` returns DoubleSpend on collision; we just
                // checked above, so this is defensive against future
                // concurrent races (the Mutex makes that impossible today).
                let reason = match e {
                    NoteError::DoubleSpend { .. } => {
                        "double-spend: race on nullifier insert".to_string()
                    }
                    other => format!("nullifier insert failed: {:?}", other),
                };
                (TurnError::InvalidEffect { reason }, path.to_vec())
            })?;
        }
        journal.record_note_nullifier_inserted(*nullifier);
        // Record for the note layer to process after turn commits.
        journal.record_note_spend(*nullifier);

        // BUG #115: validate value_commitment if present.
        // Reject malformed compressed Ristretto points immediately at apply
        // time so that the effect can never reach the finalize layer with a
        // value_commitment that is not a valid group element. The
        // conservation-proof check (Schnorr excess) and cross-note consistency
        // are verified at the finalize layer (`check_committed_conservation`).
        if let Some(vc_bytes) = value_commitment {
            if ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes)).is_none() {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "NoteSpend value_commitment is not a valid Ristretto point".into(),
                    },
                    path.to_vec(),
                ));
            }
        }

        Ok(())
    }

    /// Apply a **shielded transfer** (privacy M2-a): the opt-in privacy upgrade of
    /// the cleartext note path. The cleartext value is never seen; the executor
    /// admits the transfer on three independent gates, all fail-closed:
    ///
    /// 1. **Hidden STARK side** — every input's membership in the commitment tree
    ///    + correct nullifier derivation, proved through `HidingFriPcs` (owner /
    ///    key / Merkle path blind). Reconstructed from the wire payload and
    ///    verified by `ShieldedTransfer::verify_stark_side`, which also rejects an
    ///    in-transfer duplicate nullifier.
    /// 2. **Hidden Pedersen side** — `Σ C_in = Σ C_out` (value conserved, blind)
    ///    AND one in-`[0,2^64)` range proof per output (the negative-value /
    ///    mod-order-wrap inflation gate), over the SAME Fiat-Shamir transcript that
    ///    binds the STARK nullifiers + value-bindings (no cross-transfer splice).
    /// 3. **Cross-transfer double-spend gate** — each revealed nullifier is
    ///    consumed once in the production `note_nullifiers` set (journaled, so a
    ///    later-failing turn unwinds the spend), exactly as `NoteSpend`.
    ///
    /// NAMED RESIDUAL (honest): (a) the LIGHT-CLIENT witness — this VERIFIES live
    /// in a re-executing validator, but binding the shielded-proof verification
    /// into the `effect_vm` descriptor (so a pure light client witnesses it) is the
    /// VK-affecting follow-up. (b) the leaf↔leg VALUE LINK — the STARK proves a
    /// hidden leaf value and the Pedersen side conserves the legs, both bound to one
    /// transcript, but their cryptographic equality is only checkable with the
    /// secret opening; M2-a relies on the honest prover for it (the `verify_value_link`
    /// residual named in `circuit-prove/src/shielded/mod.rs`).
    ///
    /// Requires a `prover`-enabled build (the hiding uni-STARK verifier lives in
    /// `dregg-circuit-prove`). A verify-only build fails the effect closed.
    #[cfg(feature = "prover")]
    fn apply_shielded_transfer(
        &self,
        path: &[usize],
        journal: &mut LedgerJournal,
        payload: &crate::action::ShieldedTransferPayload,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        use dregg_circuit_prove::shielded::{ShieldedTransfer, ShieldedValueLeg};

        let invalid = |reason: String| (TurnError::InvalidEffect { reason }, path.to_vec());

        // Reconstruct the published shielded transfer from its wire payload,
        // deserializing each hidden note-spend proof.
        let leg = |l: &crate::action::ShieldedLeg| ShieldedValueLeg {
            asset_type: l.asset_type,
            commitment_bytes: l.commitment_bytes,
        };
        let transfer = ShieldedTransfer::from_serialized_parts(
            payload.merkle_root,
            payload
                .inputs
                .iter()
                .map(|i| (i.nullifier, i.value_binding, i.proof.clone()))
                .collect(),
            payload.input_legs.iter().map(leg).collect(),
            payload.output_legs.iter().map(leg).collect(),
            payload.output_range_proofs.clone(),
        )
        .map_err(|e| invalid(format!("shielded transfer payload malformed: {e}")))?;

        // GATE 1: the hidden STARK side — per-input membership + nullifier
        // derivation (owner/key/path blind), and no in-transfer duplicate.
        transfer
            .verify_stark_side()
            .map_err(|e| invalid(format!("shielded STARK verification failed: {e}")))?;
        // The structural inflation gate: exactly one range proof per output.
        transfer
            .check_range_proof_shape()
            .map_err(|e| invalid(format!("shielded range-proof shape rejected: {e}")))?;

        // GATE 2: the hidden Pedersen side — conservation (Σ in = Σ out) AND each
        // output's range proof, over the transfer's binding transcript.
        let message = transfer.transfer_message();
        dregg_cell_crypto::value_commitment::verify_full_conservation_bytes(
            &transfer.input_commitment_bytes(),
            &transfer.output_commitment_bytes(),
            &payload.conservation,
            &transfer.output_range_proofs,
            &message,
        )
        .map_err(|e| invalid(format!("shielded value conservation/range rejected: {e:?}")))?;

        // GATE 3: consume each input nullifier ONCE in the production set. The
        // shielded nullifier is a BabyBear field element; we domain-separate it to
        // a 32-byte set key so it never collides with the cleartext note-nullifier
        // space. Each insert is journaled so a later-failing turn unwinds the spend.
        let nullifiers: Vec<Nullifier> = transfer
            .nullifiers()
            .iter()
            .map(|nf| shielded_nullifier_key(nf.as_u32()))
            .collect();
        {
            let mut set = self.note_nullifiers.lock().unwrap();
            // Pre-check all (so a partial spend never lands on a double-spend).
            for nf in &nullifiers {
                if set.contains(nf) {
                    return Err(invalid(
                        "double-spend: shielded nullifier already in note_nullifiers set".into(),
                    ));
                }
            }
            for nf in &nullifiers {
                set.insert(*nf).map_err(|e| {
                    invalid(match e {
                        NoteError::DoubleSpend { .. } => {
                            "double-spend: race on shielded nullifier insert".into()
                        }
                        other => format!("shielded nullifier insert failed: {other:?}"),
                    })
                })?;
            }
        }
        for nf in &nullifiers {
            journal.record_note_nullifier_inserted(*nf);
            journal.record_note_spend(*nf);
        }

        Ok(())
    }

    /// Verify-only builds cannot admit a shielded transfer: the hiding uni-STARK
    /// verifier lives in `dregg-circuit-prove` (the `prover` surface). Fail closed.
    #[cfg(not(feature = "prover"))]
    fn apply_shielded_transfer(
        &self,
        path: &[usize],
        _journal: &mut LedgerJournal,
        _payload: &crate::action::ShieldedTransferPayload,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        Err((
            TurnError::InvalidEffect {
                reason: "shielded transfer requires a prover-enabled build (no shielded \
                         verifier linked in this verify-only executor)"
                    .into(),
            },
            path.to_vec(),
        ))
    }

    // ─── Reactive effects (Track 2): Promise / Notify / React ────────────────
    //
    // The keystone (REACTIVE-EFFECTS.md §6): a promise-hole IS a nullifier. To
    // `React` is to SPEND the hole. The executor enforces one-shotness with the
    // SAME production `note_nullifiers` set that gates `NoteSpend`: the hole's
    // 32-byte id is the nullifier, so a second react (or a replayed hole-id) is
    // rejected by the identical double-spend gate. The in-circuit witness (the
    // React descriptor mirroring `noteSpendV3`'s grow-gate) reads exactly this
    // nullifier — see the report.

    /// Deposit a STANDING COMMITMENT (a promise-hole) in the reactive registry.
    /// `cell` commits to run `wake` once `resolution_condition` holds. The hole's
    /// id is the wake-turn hash — the key a later [`Effect::React`] spends.
    fn apply_promise(
        &self,
        path: &[usize],
        actor: &CellId,
        cell: &CellId,
        resolution_condition: &crate::pending::ResolutionCondition,
        wake: &Turn,
        timeout_height: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // The committing cell must be the actor (a cell makes its OWN standing
        // commitments — no cross-cell promise injection).
        if cell != actor {
            return Err((
                TurnError::InvalidEffect {
                    reason: "Promise: the committing cell must be the actor".into(),
                },
                path.to_vec(),
            ));
        }
        let mut reg = self.reactive_registry.lock().unwrap();
        reg.submit_pending_at(
            wake.clone(),
            resolution_condition.clone(),
            timeout_height,
            self.block_height,
        );
        Ok(())
    }

    /// Deposit a WAKE (a promise-hole) in the recipient's reactive registry — the
    /// kernel-backed `NotifyEdge`. `to` commits to run `wake` once it discharges
    /// `resolution_condition`. The hole id (the wake-turn hash) is what a later
    /// [`Effect::React`] from `to` spends.
    #[allow(clippy::too_many_arguments)]
    fn apply_notify(
        &self,
        path: &[usize],
        actor: &CellId,
        from: &CellId,
        to: &CellId,
        wake: &Turn,
        resolution_condition: &crate::pending::ResolutionCondition,
        timeout_height: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // The sender must be the actor (a cell wakes peers under its OWN
        // provenance — no spoofed `from`).
        if from != actor {
            return Err((
                TurnError::InvalidEffect {
                    reason: "Notify: the sender (from) must be the actor".into(),
                },
                path.to_vec(),
            ));
        }
        // The deposited wake is the turn the RECIPIENT runs on react — its agent
        // must be the recipient (the hole is the recipient's to discharge).
        if &wake.agent != to {
            return Err((
                TurnError::InvalidEffect {
                    reason: "Notify: the wake turn's agent must be the recipient (to)".into(),
                },
                path.to_vec(),
            ));
        }
        let mut reg = self.reactive_registry.lock().unwrap();
        reg.submit_pending_at(
            wake.clone(),
            resolution_condition.clone(),
            timeout_height,
            self.block_height,
        );
        Ok(())
    }

    /// REACT: discharge a promise-hole by presenting a proof of `condition`. THE
    /// ONE-SHOT SPEND. The hole `pending_id` is spent into the production
    /// `note_nullifiers` set EXACTLY as a [`Effect::NoteSpend`] nullifier:
    ///
    ///  1. Bind the spent nullifier to the resolved turn: `wake.hash()` MUST
    ///     equal `pending_id` (a react cannot spend one hole while resolving
    ///     another — the nullifier-to-turn binding the circuit witnesses).
    ///  2. Verify the proof discharges the condition (the genuine resolution
    ///     gate — wrong/expired proofs are refused and spend nothing).
    ///  3. SPEND `pending_id` into `note_nullifiers` with double-spend
    ///     rejection (journaled). A second react — or a replay of the same
    ///     `pending_id` — hits the identical gate `NoteSpend` rides and is
    ///     REJECTED. THIS is the one-shot tooth the light client witnesses.
    ///  4. If a matching hole is live in the reactive registry, RESOLVE it with
    ///     a genuine receipt over the resolved turn (the registry-removal is a
    ///     redundant second tooth; the nullifier gate is load-bearing).
    fn apply_react(
        &self,
        path: &[usize],
        journal: &mut LedgerJournal,
        pending_id: &Nullifier,
        condition: &crate::conditional::ProofCondition,
        resolution_proof: &crate::conditional::ConditionProof,
        wake: &Turn,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // The hole id must be well-formed (non-zero) — the same guard NoteSpend
        // applies to its nullifier.
        if pending_id.0.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null pending_id in React".into(),
                },
                path.to_vec(),
            ));
        }

        // (1) NULLIFIER↔TURN BINDING: the spent hole id IS the resolved turn's
        // hash. Without this, a react could spend an arbitrary nullifier while
        // claiming to resolve an unrelated wake.
        let wake_hash = wake.hash();
        if wake_hash != pending_id.0 {
            return Err((
                TurnError::InvalidEffect {
                    reason: "React: wake turn hash does not equal pending_id (nullifier↔turn \
                             binding violated)"
                        .into(),
                },
                path.to_vec(),
            ));
        }

        // (2) GENUINE RESOLUTION GATE: the proof must discharge the condition.
        // `resolve_condition` enforces the temporal bound (timeout) and proof
        // validity. We use a transient proof-hash ledger because the PERMANENT
        // one-shot gate is the nullifier set below (the hole id), which is
        // stronger: it rejects the spend even if the same hole were re-presented
        // with a fresh proof.
        let mut transient_proof_ledger = std::collections::HashSet::new();
        // The hole's timeout is carried by the registry entry when known;
        // otherwise the condition is evaluated at the current height with no
        // separate expiry (the timeout tooth lives in the registry/notify path).
        let timeout_height = {
            let reg = self.reactive_registry.lock().unwrap();
            reg.get_pending(&pending_id.0)
                .map(|e| e.timeout_height)
                .unwrap_or(u64::MAX)
        };
        let verdict = crate::conditional::resolve_condition(
            condition,
            resolution_proof,
            self.block_height,
            timeout_height,
            &[],
            crate::conditional::DEFAULT_MAX_ROOT_AGE,
            &mut transient_proof_ledger,
            &[],
        );
        match verdict {
            crate::conditional::ConditionalResult::Resolved => {}
            crate::conditional::ConditionalResult::Pending => {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "React: condition not yet satisfied".into(),
                    },
                    path.to_vec(),
                ));
            }
            crate::conditional::ConditionalResult::Expired => {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "React: hole expired (past its timeout height)".into(),
                    },
                    path.to_vec(),
                ));
            }
            crate::conditional::ConditionalResult::InvalidProof(reason) => {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!("React: proof rejected: {reason}"),
                    },
                    path.to_vec(),
                ));
            }
        }

        // (3) THE ONE-SHOT SPEND — insert the hole id into the production
        // nullifier set with double-spend rejection. This is the SAME gate
        // `apply_note_spend` uses; react-twice (or a replayed pending_id) is a
        // double-spend and is rejected here. Journaled so a turn that fails
        // AFTER this point unwinds the insert (no permanent hole-burn on a
        // deliberate-failure attack).
        {
            let mut set = self.note_nullifiers.lock().unwrap();
            if set.contains(pending_id) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "React: double-spend — pending_id already reacted (one-shot)"
                            .into(),
                    },
                    path.to_vec(),
                ));
            }
            set.insert(*pending_id).map_err(|e| {
                let reason = match e {
                    NoteError::DoubleSpend { .. } => {
                        "React: double-spend — race on pending_id insert".to_string()
                    }
                    other => format!("React: pending_id insert failed: {other:?}"),
                };
                (TurnError::InvalidEffect { reason }, path.to_vec())
            })?;
        }
        journal.record_note_nullifier_inserted(*pending_id);
        journal.record_note_spend(*pending_id);

        // (4) RESOLVE the hole with a GENUINE receipt over the resolved turn.
        // The receipt is content-addressed to the wake turn we just verified
        // (its hash == pending_id), so the registry cascade has a real, bound
        // provenance link. If no live hole exists (a bare react against a hole
        // notified out-of-band), the nullifier spend above already enforced
        // one-shotness — the registry removal is a redundant tooth, not a gate.
        {
            let mut reg = self.reactive_registry.lock().unwrap();
            if reg.get_pending(&pending_id.0).is_some() {
                let receipt = genuine_resolution_receipt(wake);
                let _events = reg.resolve(
                    pending_id.0,
                    crate::pending::ResolutionOutcome::Resolved(receipt),
                );
            }
        }

        Ok(())
    }

    fn apply_note_create(
        &self,
        path: &[usize],
        journal: &mut LedgerJournal,
        commitment: &NoteCommitment,
        // BUG #115: previously dropped via `..`; now validated at apply time.
        // If `value_commitment` is present, `range_proof` must also be present
        // and must verify against the commitment. This is defense-in-depth:
        // the finalize layer (`verify_output_range_proofs`) also checks this
        // for the Committed conservation path, but we reject here early so
        // that malformed effects never reach the journal.
        value_commitment: Option<&[u8; 32]>,
        range_proof: Option<&[u8]>,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Validate commitment is well-formed (non-zero).
        if commitment.0.iter().all(|&b| b == 0) {
            return Err((
                TurnError::InvalidEffect {
                    reason: "null commitment in NoteCreate".into(),
                },
                path.to_vec(),
            ));
        }
        // Note: zero-value notes are legitimate (e.g., NFTs where asset_type
        // is the unique identifier and value=0 represents ownership).

        // BUG #115 (defense-in-depth): validate value_commitment + range_proof
        // at apply time. The finalize layer also checks this, but we reject
        // early so that malformed effects never persist through the journal.
        //
        // Rules:
        //   (a) value_commitment, if present, must be a valid compressed
        //       Ristretto point.
        //   (b) if value_commitment is present, range_proof must also be
        //       present and non-empty, and must verify against the commitment.
        //       This prevents a prover from hiding a negative value behind a
        //       commitment without proving the value is in [0, 2^64).
        //   (c) range_proof without value_commitment is incoherent — reject.
        match (value_commitment, range_proof) {
            (None, None) => {
                // Cleartext path: no commitment, no range proof — OK.
            }
            (None, Some(_)) => {
                return Err((
                    TurnError::InvalidEffect {
                        reason: "NoteCreate has range_proof but no value_commitment".into(),
                    },
                    path.to_vec(),
                ));
            }
            (Some(vc_bytes), rp_opt) => {
                // Decode the compressed Ristretto point.
                let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes)).ok_or_else(
                    || {
                        (
                            TurnError::InvalidEffect {
                                reason:
                                    "NoteCreate value_commitment is not a valid Ristretto point"
                                        .into(),
                            },
                            path.to_vec(),
                        )
                    },
                )?;
                // Range proof is required when a value commitment is present.
                let rp_bytes = rp_opt.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "NoteCreate has value_commitment but no range_proof".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if rp_bytes.is_empty() {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "NoteCreate range_proof is empty".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the Bulletproof range proof against the commitment.
                let bulletproof = BulletproofRangeProof {
                    proof_bytes: rp_bytes.to_vec(),
                };
                bulletproof.verify_range(&vc).map_err(|e| {
                    (
                        TurnError::InvalidEffect {
                            reason: format!("NoteCreate range proof verification failed: {}", e),
                        },
                        path.to_vec(),
                    )
                })?;
            }
        }

        // Record for the note layer to process after turn commits.
        journal.record_note_create(*commitment);
        Ok(())
    }

    // BridgeMint: verify the portable proof against trusted federation roots
    // and track the nullifier to prevent double-bridge attacks.
    // The destination_federation in the proof must match our local_federation_id
    // to prevent cross-federation replay (inflation bug).
    //
    // The note-spending AIR's pi layout (post-DSL upgrade) is:
    //   pi[0] = nullifier
    //   pi[1] = merkle_root
    //   pi[2] = value
    //   pi[3] = asset_type
    //   pi[4] = destination_federation
    // The boundary constraint at row 0 col 18 = pi[4] pins the prover's
    // trace destination to whatever the verifier passes — so a proof
    // generated with dest_federation D fails verification if the
    // verifier passes D' != D. Combined with `verify_portable_note`'s
    // local-federation-id check, this closes the cross-federation
    // replay trapdoor (see AUDIT-nullifiers.md §5).
    fn apply_bridge_mint(
        &self,
        path: &[usize],
        journal: &mut LedgerJournal,
        portable_proof: &PortableNoteProof,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // PROOF-TO-ACTION BINDING (Lane Bridge-Implementation).
        //
        // Previously, the bridge proof verification path serialized
        // (nullifier || root || value || asset_type || destination_federation)
        // into a byte buffer and passed it to `ProofVerifier::verify(..)`
        // as the `vk` argument. That argument is consumed as a 32-byte
        // verification key (the first 4 bytes are treated as a BabyBear
        // felt for the federation-root check), so all 112 typed PI bytes
        // were silently truncated — the four cryptographic bindings the
        // AIR enforces (nullifier, value, asset_type, destination) were
        // never compared against the proof's embedded PI vector.
        //
        // The fix: skip the generic `ProofVerifier` trait entirely for
        // bridge mints and check the proof against the typed 7-slot claim
        // tuple through the IR-v2 descriptor prover (`verify_note_spend_descriptor2`
        // → `verify_vm_descriptor2` over the fail-closed `note-spend-leaf`
        // descriptor). This verifier:
        //
        //   * decodes the postcard(Ir2BatchProof) wire blob,
        //   * rebuilds the descriptor's public-input vector over the typed PI
        //     (nullifier, merkle_root, value_lo, asset_type,
        //     destination_federation, value_hi, mint_hash),
        //   * algebraically rejects any proof whose trace columns at row 0
        //     (col::NULLIFIER, col::VALUE, col::VALUE_HI, col::ASSET_TYPE,
        //     col::DESTINATION_FEDERATION), whose last-row Merkle root, or
        //     whose in-AIR mint-hash do not match the PI vector that the
        //     executor supplies from the `PortableNoteProof`.
        //
        // Combined with `verify_portable_note`'s local-federation-id check
        // and `BridgedNullifierSet::insert`'s replay protection, this
        // closes the cross-federation replay, value-inflation, asset-type
        // confusion, and recipient-substitution trapdoors (AUDIT-nullifiers.md
        // §5; BACKWATER-CRATES-AUDIT.md bridge/ open issue).
        //
        // PI encoding convention (provers MUST match):
        //   * nullifier, merkle_root, destination_federation: 32-byte values
        //     compressed into one BabyBear via
        //     `BabyBear::encode_hash(bytes)` → Poseidon2 `hash_many` →
        //     single field element (the same `bytes_to_babybear`
        //     compression used by `bridge::present` and the SDK).
        //   * value: split into TWO limbs — low 30 bits (PI[VALUE], the felt
        //     in the note commitment) + upper 34 bits (PI[VALUE_HI]). The
        //     proof now binds the FULL u64 amount, closing the 30-bit
        //     truncation gap (CAVEAT-LAYER-COVERAGE.md §6.5).
        //   * asset_type: low-30 bits of the u64 reduced mod the BabyBear
        //     prime as a canonical `BabyBear::new` element (asset tags are
        //     small enumerated identifiers, not balances). The prover must
        //     place the same value into `witness.value` / `witness.asset_type`
        //     to satisfy the boundary constraint.
        let verify_stark = |nullifier: &[u8; 32],
                            root: &[u8; 32],
                            dest_federation: &[u8; 32],
                            value: u64,
                            asset_type: u64,
                            proof_bytes: &[u8]|
         -> Result<(), String> {
            use dregg_circuit::BabyBear;
            use dregg_circuit::poseidon2;

            // Compress a 32-byte value to a single BabyBear via Poseidon2 of 8 limbs.
            // Matches `bridge::present::bytes_to_babybear` so prover and verifier agree.
            fn compress(bytes: &[u8; 32]) -> BabyBear {
                let limbs = BabyBear::encode_hash(bytes);
                poseidon2::hash_many(&limbs)
            }
            // 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): split a u64
            // into (low 30 bits, upper 34 bits). The low limb is the field
            // element that participates in the note commitment; the high limb
            // is bound separately into the proof's PI[VALUE_HI] slot. Both
            // limbs are < p so each is a canonical BabyBear. A u64 above 2^30
            // now produces a non-zero high limb that the AIR boundary
            // constraint pins, so two amounts differing above bit 30 can no
            // longer share a proof.
            fn u64_to_limbs(v: u64) -> (BabyBear, BabyBear) {
                let lo = (v & ((1u64 << 30) - 1)) as u32;
                let hi = (v >> 30) as u32; // fits in u32 since v < 2^64
                (BabyBear::new(lo), BabyBear::new(hi))
            }

            let nullifier_bb = compress(nullifier);
            let root_bb = compress(root);
            let dest_bb = compress(dest_federation);
            let (value_lo, value_hi) = u64_to_limbs(value);
            // asset_type stays a single felt: asset identifiers are small
            // enumerated tags, not balances, so 30-bit binding is faithful.
            let asset_bb = BabyBear::new((asset_type & ((1u64 << 30) - 1)) as u32);

            // SECURITY: This rejects any IR-v2 batch proof whose embedded PI
            // vector does not match the 7-slot claim tuple
            // (nullifier_bb, root_bb, value_lo, asset_bb, dest_bb, value_hi,
            // mint_hash). The note-spend descriptor's boundary pins over
            // {NULLIFIER, VALUE, VALUE_HI, ASSET_TYPE, DESTINATION_FEDERATION},
            // the last-row Merkle-root pin, and the MINT_HASH pin bind the
            // prover's trace to whatever the verifier passes here — including
            // the FULL u64 amount via the two value limbs.
            verify_note_spend_descriptor2(
                nullifier_bb,
                root_bb,
                value_lo,
                value_hi,
                asset_bb,
                dest_bb,
                proof_bytes,
            )
        };

        dregg_cell_crypto::note_bridge::verify_portable_note(
            portable_proof,
            &self.local_federation_id,
            &self.trusted_federation_roots,
            verify_stark,
        )
        .map_err(|e| {
            (
                TurnError::BridgeMintFailed {
                    reason: e.to_string(),
                },
                path.to_vec(),
            )
        })?;

        self.bridged_nullifiers
            .lock()
            .unwrap()
            .insert(portable_proof.nullifier)
            .map_err(|e| {
                (
                    TurnError::BridgeMintFailed {
                        reason: e.to_string(),
                    },
                    path.to_vec(),
                )
            })?;

        // Record the insertion so it can be rolled back on turn failure.
        // Without this, an attacker could craft a turn with BridgeMint +
        // deliberate failure to permanently burn a nullifier without minting.
        journal.record_bridged_nullifier_inserted(portable_proof.nullifier);

        Ok(())
    }

    // BridgeLock: Phase 1 — lock a note for conditional cross-federation transfer.
    // The note's nullifier is committed-to but NOT added to the permanent set.
    // Instead a PendingBridge record is created in pending_bridges.

    // BridgeFinalize: Phase 3 — present a destination receipt to finalize the burn.

    // BridgeCancel: Phase 4 — cancel a bridge after timeout (value returned to owner).

    // Obligation effects: validate structure, enforce balance movement,
    // and record for the obligation registry.

    // Escrow effects: conditional settlement with timeout refund.
    // Committed escrow effects: privacy-preserving conditional settlement.

    // ExerciseViaCapability: one-step evaluation map.
    // Look up cap_slot in actor's c-list, verify permissions, execute
    // inner_effects against the capability's target cell.
    fn apply_exercise_via_capability(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        actor: &CellId,
        journal: &mut LedgerJournal,
        cap_slot: u32,
        inner_effects: &[Effect],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let actor_cell = ledger
            .get(actor)
            .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;

        // Look up the capability by slot.
        let cap = actor_cell
            .capabilities
            .lookup(cap_slot)
            .cloned()
            .ok_or_else(|| {
                (
                    TurnError::CapabilityNotHeld {
                        actor: *actor,
                        target: CellId::from_bytes([0u8; 32]), // slot doesn't exist
                    },
                    path.to_vec(),
                )
            })?;

        let cap_target = cap.target;

        // Check capability expiry.
        if let Some(expires_at) = cap.expires_at {
            if self.block_height > expires_at {
                return Err((
                    TurnError::CapabilityNotHeld {
                        actor: *actor,
                        target: cap_target,
                    },
                    path.to_vec(),
                ));
            }
        }

        // Check revocation channel: if the capability has a breadstuff that
        // matches a revocation channel, verify the channel is still active.
        if let Some(ref channels) = self.revocation_channels {
            if let Some(breadstuff) = &cap.breadstuff {
                // Use the breadstuff as a potential channel_id (capabilities
                // gated by a revocation channel store the channel_id as breadstuff).
                if let Err(_) = channels.check_exercise_permitted(
                    breadstuff,
                    self.block_height,
                    self.block_height, // assume fresh check at current height
                    self.max_introduction_lifetime,
                ) {
                    // Check if this is actually a registered channel (not just any breadstuff).
                    if channels.get(breadstuff).is_some() {
                        return Err((
                            TurnError::CapabilityRevoked {
                                actor: *actor,
                                channel_id: *breadstuff,
                                tripped_at: self.block_height,
                            },
                            path.to_vec(),
                        ));
                    }
                }
            }
        }

        // Verify the target cell exists.
        let target_cell_ref = ledger
            .get(&cap_target)
            .ok_or_else(|| (TurnError::CellNotFound { id: cap_target }, path.to_vec()))?;

        // R7 epoch-at-retrieval (DREGG3 §6): a STORED capability must not
        // survive its grantor's revocation. When the cap carries a
        // delegation-snapshot stamp (`stored_epoch: Some(e)`), re-check it
        // against the grantor's CURRENT delegation_epoch at exercise time.
        // The grantor of authority over `cap_target` is `cap_target` itself
        // (the self-grant origin; its epoch is bumped by its
        // `RevokeDelegation`s) — conservatively, ANY grantor epoch-bump
        // stales earlier-stored caps; the holder's duty is to refresh.
        //
        // ⚠ MIGRATION WINDOW (loud): `stored_epoch: None` = a direct grant
        // OR a pre-R7 persisted cap — both are EXEMPT from this check until
        // re-granted with a snapshot stamp.
        if let Some(stored) = cap.stored_epoch {
            let current_epoch = target_cell_ref.state.delegation_epoch();
            if stored < current_epoch {
                return Err((
                    TurnError::CapabilityStale {
                        actor: *actor,
                        grantor: cap_target,
                        stored_epoch: stored,
                        current_epoch,
                    },
                    path.to_vec(),
                ));
            }
        }

        // Permission check: the capability's permissions must allow the operations.
        // If the capability requires Impossible, reject.
        if matches!(cap.permissions, dregg_cell::AuthRequired::Impossible) {
            return Err((
                TurnError::PermissionDenied {
                    cell: cap_target,
                    action: "ExerciseViaCapability".to_string(),
                    required: dregg_cell::AuthRequired::Impossible,
                },
                path.to_vec(),
            ));
        }

        // Also check that the capability's permission level satisfies the
        // TARGET CELL's requirements for each inner effect's operation.
        // This prevents bypassing target cell permissions via capability exercise.
        for inner_effect in inner_effects.iter() {
            // SECURITY (#111): Transfer with from != cap_target must be gated too.
            // Previously only `from == cap_target` matched the Send arm, so any
            // Transfer that names a third cell as `from` fell through to `_ => None`
            // and skipped both the cap-target permission check and the explicit
            // cap-to-from check.  Fix: handle all Transfer variants explicitly.
            if let Effect::Transfer { from, .. } = inner_effect {
                if from != &cap_target {
                    // The actor must hold an explicit capability covering `from`.
                    // We re-use check_cross_cell_permission which verifies both the
                    // c-list entry and `from`'s Send permission level.
                    self.check_cross_cell_permission(
                        ledger,
                        actor,
                        from,
                        dregg_cell::permissions::Action::Send,
                        "Send (Transfer.from via ExerciseViaCapability)",
                        dregg_cell::EFFECT_TRANSFER,
                        path,
                    )?;
                    // Handled; skip the generic required_perm_action path below.
                    continue;
                }
            }

            let required_perm_action = match inner_effect {
                Effect::SetField { .. } => {
                    Some((dregg_cell::permissions::Action::SetState, "SetState"))
                }
                Effect::Transfer { from, .. } if from == &cap_target => {
                    Some((dregg_cell::permissions::Action::Send, "Send"))
                }
                Effect::IncrementNonce { .. } => Some((
                    dregg_cell::permissions::Action::IncrementNonce,
                    "IncrementNonce",
                )),
                Effect::GrantCapability { .. } => {
                    Some((dregg_cell::permissions::Action::Delegate, "Delegate"))
                }
                Effect::RevokeCapability { .. } => {
                    Some((dregg_cell::permissions::Action::Delegate, "Delegate"))
                }
                Effect::SetPermissions { .. } => Some((
                    dregg_cell::permissions::Action::SetPermissions,
                    "SetPermissions",
                )),
                Effect::SetVerificationKey { .. } => Some((
                    dregg_cell::permissions::Action::SetVerificationKey,
                    "SetVerificationKey",
                )),
                Effect::SetProgram { .. } => Some((
                    dregg_cell::permissions::Action::SetVerificationKey,
                    "SetProgram",
                )),
                _ => None,
            };

            if let Some((perm_action, action_name)) = required_perm_action {
                let target_required = target_cell_ref.permissions.for_action(perm_action);
                // The target cell's permission must be satisfiable by the capability's
                // permission level. If the target requires Impossible, always reject.
                // If the target requires Signature/Proof/Either but the capability only
                // grants None-level access, that's insufficient.
                if matches!(target_required, AuthRequired::Impossible) {
                    return Err((
                        TurnError::PermissionDenied {
                            cell: cap_target,
                            action: action_name.to_string(),
                            required: target_required.clone(),
                        },
                        path.to_vec(),
                    ));
                }
                // If the target requires auth (Signature/Proof/Either) and the
                // capability's permission level is weaker (None), reject.
                // The capability permission acts as the auth level the actor provides.
                if !matches!(target_required, AuthRequired::None) {
                    // The capability must be at least as strong as what the target requires.
                    if !cap.permissions.is_narrower_or_equal(target_required) {
                        return Err((
                            TurnError::PermissionDenied {
                                cell: cap_target,
                                action: action_name.to_string(),
                                required: target_required.clone(),
                            },
                            path.to_vec(),
                        ));
                    }
                }
            }
        }

        // Facet enforcement: if the capability has an allowed_effects mask,
        // verify that every inner effect's kind is permitted by the mask.
        // This implements E-language facets — a restricted view of the target
        // cell's interface through this capability.
        //
        // KERNEL ALIGNMENT: route through the canonical `is_effect_permitted`
        // (the P2-1 fail-closed semantics) rather than an inlined `mask != 0`
        // skip. The verified kernel's facet gate (`innerFacetsAdmittedA` over
        // `capFacetMaskA`, TurnExecutorFull.lean:2483) admits an inner effect
        // only when its required facet lies in the held cap's mask, and an
        // empty mask (`endpoint _ []` / the `null` cap) admits NOTHING. The
        // inlined `mask != 0` treated an explicitly-empty facet `Some(0)` as
        // UNRESTRICTED — re-opening the very hole the `is_effect_permitted`
        // P2-1 fix closed: an `allowed_effects: Some(0)` cap would admit every
        // inner effect, where the verified kernel refuses all. `None` (no
        // mask) remains the full-facet node cap (`is_effect_permitted` returns
        // `true`), matching `capFacetMaskA (.node _) = nodeFacets`.
        if cap.allowed_effects.is_some() {
            for inner_effect in inner_effects.iter() {
                let effect_bit = inner_effect.effect_kind_mask();
                if !dregg_cell::is_effect_permitted(cap.allowed_effects, effect_bit) {
                    return Err((
                        TurnError::FacetViolation {
                            actor: *actor,
                            target: cap_target,
                            cap_slot,
                            attempted_effect: format!("{:?}", std::mem::discriminant(inner_effect)),
                            allowed_mask: cap.allowed_effects.unwrap_or(0),
                        },
                        path.to_vec(),
                    ));
                }
            }
        }

        // Execute each inner effect against the capability's target cell.
        for inner_effect in inner_effects {
            self.apply_effect(inner_effect, ledger, path, &cap_target, actor, journal)?;
        }

        Ok(())
    }

    // PipelinedSend must be resolved by the pipeline executor's resolution pass
    // before the turn reaches apply_effect. If we get here, it means the turn
    // was executed outside of a pipeline without resolution — which is a bug.
    fn apply_pipelined_send(
        &self,
        path: &[usize],
        target: &crate::eventual::EventualRef,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        Err((
            TurnError::PreconditionFailed {
                description: format!(
                    "unresolved PipelinedSend to EventualRef(source {:02x}{:02x}.., slot {}); \
                     turn must be executed within a pipeline",
                    target.source_turn[0], target.source_turn[1], target.output_slot
                ),
            },
            path.to_vec(),
        ))
    }

    // === Sealer/Unsealer effects (E-style rights amplification) ===

    fn apply_introduce(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        introducer: &CellId,
        recipient: &CellId,
        target: &CellId,
        permissions: &dregg_cell::AuthRequired,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let intro_cell = ledger
            .get(introducer)
            .ok_or_else(|| (TurnError::CellNotFound { id: *introducer }, path.to_vec()))?;
        if !intro_cell.capabilities.has_access(recipient) {
            return Err((
                TurnError::IntroductionDenied {
                    introducer: *introducer,
                    recipient: *recipient,
                    target: *target,
                    reason: "introducer has no capability to recipient".to_string(),
                },
                path.to_vec(),
            ));
        }
        let held_cap = intro_cell
            .capabilities
            .lookup_by_target(target)
            .ok_or_else(|| {
                (
                    TurnError::IntroductionDenied {
                        introducer: *introducer,
                        recipient: *recipient,
                        target: *target,
                        reason: "introducer has no capability to target".to_string(),
                    },
                    path.to_vec(),
                )
            })?;
        // KERNEL ALIGNMENT / authority-over-time: the introducer's held cap must
        // be LIVE at the current height. The exercise path
        // (`apply_exercise_via_capability`) already refuses an expired cap; the
        // introduce path looked up the held cap with the non-height-aware
        // `lookup_by_target` and never consulted `expires_at`, so an introducer
        // could mint a FRESH cap (`grant_with_expiry`) for a recipient FROM an
        // already-lapsed cap — re-introducing authority that should have died.
        // The verified kernel's edge/hold gate is snapshot-correct (an absent /
        // dead conferring edge admits nothing); an expired held edge confers no
        // introduction authority. Fail-closed on a lapsed held cap.
        if let Some(expires_at) = held_cap.expires_at {
            if self.block_height > expires_at {
                return Err((
                    TurnError::IntroductionDenied {
                        introducer: *introducer,
                        recipient: *recipient,
                        target: *target,
                        reason: "introducer's capability to target has expired".to_string(),
                    },
                    path.to_vec(),
                ));
            }
        }
        if !dregg_cell::is_attenuation(&held_cap.permissions, permissions) {
            return Err((
                TurnError::IntroductionDenied {
                    introducer: *introducer,
                    recipient: *recipient,
                    target: *target,
                    reason: "granted permissions exceed introducer's own (amplification denied)"
                        .to_string(),
                },
                path.to_vec(),
            ));
        }
        // Consent check: the target cell must allow delegation (delegate != Impossible).
        let target_cell = ledger
            .get(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        if target_cell.permissions.delegate == dregg_cell::AuthRequired::Impossible {
            return Err((
                TurnError::IntroductionDenied {
                    introducer: *introducer,
                    recipient: *recipient,
                    target: *target,
                    reason: "target cell has delegate=Impossible (consent denied)".to_string(),
                },
                path.to_vec(),
            ));
        }
        if ledger.get(recipient).is_none() {
            return Err((TurnError::CellNotFound { id: *recipient }, path.to_vec()));
        }
        let recipient_cell = ledger.get_mut(recipient).unwrap();
        let expires_at = self.block_height + self.max_introduction_lifetime;
        let granted_slot = recipient_cell
            .capabilities
            .grant_with_expiry(*target, permissions.clone(), expires_at)
            .ok_or_else(|| {
                (
                    TurnError::CapabilitySlotOverflow { cell: *recipient },
                    path.to_vec(),
                )
            })?;
        journal.record_grant_capability(*recipient, granted_slot);
        Ok(())
    }

    fn apply_spawn_with_delegation(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        child_public_key: &[u8; 32],
        child_token_id: &[u8; 32],
        max_staleness: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let parent_cell_data = ledger.get(action_target).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *action_target },
                path.to_vec(),
            )
        })?;
        let delegation_epoch = parent_cell_data.state.delegation_epoch();
        let now = self.current_timestamp as u64;
        let snapshot: Vec<dregg_cell::CapabilityRef> =
            parent_cell_data.capabilities.iter().cloned().collect();

        let child_id = CellId::derive_raw(child_public_key, child_token_id);
        let mut child_cell = Cell::with_balance(*child_public_key, *child_token_id, 0);
        child_cell.delegate = Some(*action_target);
        let clist_bytes = postcard::to_allocvec(&snapshot).unwrap_or_default();
        let clist_commitment = dregg_cell::DelegatedRef::compute_clist_commitment(&clist_bytes);
        child_cell.delegation = Some(dregg_cell::DelegatedRef::new(
            *action_target,
            child_id,
            snapshot,
            delegation_epoch,
            now,
            max_staleness,
            clist_commitment,
            [0u8; 64], // Executor-internal delegation, signature verified by execution authority.
        ));

        ledger
            .insert_cell(child_cell)
            .map_err(|_| (TurnError::CellAlreadyExists { id: child_id }, path.to_vec()))?;
        journal.record_create_cell(child_id);
        Ok(())
    }

    fn apply_refresh_delegation(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        child: &CellId,
        declared_snapshot: &[u8; 32],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Self-refresh: the declared child MUST be the acting cell. The effect
        // binds `child` into effects_hash, so a light client sees WHICH
        // delegation is re-armed; a mismatch is a forged target.
        if child != action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "RefreshDelegation child must equal the action target (self-refresh)"
                        .into(),
                },
                path.to_vec(),
            ));
        }
        let child_cell = ledger.get(action_target).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *action_target },
                path.to_vec(),
            )
        })?;
        let parent_id = child_cell.delegate.ok_or_else(|| {
            (
                TurnError::InvalidAuthorization {
                    reason: "cell has no delegate (parent) to refresh from".to_string(),
                },
                path.to_vec(),
            )
        })?;
        let max_staleness = child_cell
            .delegation
            .as_ref()
            .map(|d| d.max_staleness)
            .unwrap_or(0);
        let old_delegation = child_cell.delegation.clone();

        let parent_cell_data = ledger
            .get(&parent_id)
            .ok_or_else(|| (TurnError::CellNotFound { id: parent_id }, path.to_vec()))?;
        let new_snapshot: Vec<dregg_cell::CapabilityRef> =
            parent_cell_data.capabilities.iter().cloned().collect();
        let new_epoch = parent_cell_data.state.delegation_epoch();
        let now = self.current_timestamp as u64;

        let clist_bytes = postcard::to_allocvec(&new_snapshot).unwrap_or_default();
        let clist_commitment = dregg_cell::DelegatedRef::compute_clist_commitment(&clist_bytes);
        // THE FORGE ANTIBODY: the snapshot the effect DECLARES (bound into
        // effects_hash, so a light client trusts it) MUST equal the genuine
        // commitment derived from the parent's live c-list. A refresh claiming a
        // fabricated snapshot is refused — the on-the-wire value is forced honest.
        if &clist_commitment != declared_snapshot {
            return Err((
                TurnError::InvalidEffect {
                    reason: "RefreshDelegation snapshot does not match the parent's live c-list \
                             commitment (forged refresh)"
                        .into(),
                },
                path.to_vec(),
            ));
        }
        let child_mut = ledger.get_mut(action_target).unwrap();
        journal.record_set_delegation(*action_target, old_delegation);
        child_mut.delegation = Some(dregg_cell::DelegatedRef::new(
            parent_id,
            *action_target,
            new_snapshot,
            new_epoch,
            now,
            max_staleness,
            clist_commitment,
            [0u8; 64], // Executor-internal delegation, signature verified by execution authority.
        ));
        Ok(())
    }

    fn apply_revoke_delegation(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        child: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let child_cell = ledger
            .get(child)
            .ok_or_else(|| (TurnError::CellNotFound { id: *child }, path.to_vec()))?;
        if child_cell.delegate != Some(*action_target) {
            return Err((
                TurnError::DelegationDenied {
                    parent: *action_target,
                    child_target: *child,
                },
                path.to_vec(),
            ));
        }
        let old_child_delegation = child_cell.delegation.clone();

        let parent_mut = ledger.get_mut(action_target).unwrap();
        let old_epoch = parent_mut.state.delegation_epoch();
        journal.record_set_delegation_epoch(*action_target, old_epoch);
        if !parent_mut.state.bump_delegation_epoch() {
            return Err((
                TurnError::NonceOverflow {
                    cell: *action_target,
                },
                path.to_vec(),
            ));
        }

        let child_mut = ledger.get_mut(child).unwrap();
        journal.record_set_delegation(*child, old_child_delegation);
        child_mut.delegation = None;
        Ok(())
    }

    fn apply_make_sovereign(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        cell: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Only the cell itself (as action target) can make itself sovereign.
        if cell != action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "MakeSovereign cell must match action target".into(),
                },
                path.to_vec(),
            ));
        }
        // KERNEL ALIGNMENT (lifecycle liveness): the verified `makeSovereignStep`
        // (`TurnExecutorFull.lean:1606`) gates `acceptsEffects target` (Live-ONLY).
        // Caps survive `destroy`, so an authority-only gate would let a
        // Destroyed/Sealed cell be made sovereign ("Destroyed is terminal").
        // `make_sovereign` itself does NOT check lifecycle, so gate here.
        {
            let c = ledger
                .get(cell)
                .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
            if !c.is_live() {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "MakeSovereign target cell {cell} is not live (sealed/destroyed)"
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }
        // Transition the cell from hosted to sovereign.
        ledger.make_sovereign(cell).map_err(|e| {
            (
                TurnError::InvalidEffect {
                    reason: format!("MakeSovereign failed: {e}"),
                },
                path.to_vec(),
            )
        })?;
        Ok(())
    }

    fn apply_create_cell_from_factory(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        journal: &mut LedgerJournal,
        factory_vk: &[u8; 32],
        owner_pubkey: &[u8; 32],
        token_id: &[u8; 32],
        params: &dregg_cell::factory::FactoryCreationParams,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if params.owner_pubkey != *owner_pubkey {
            return Err((
                TurnError::InvalidEffect {
                    reason: "factory creation owner_pubkey must match params.owner_pubkey"
                        .to_string(),
                },
                path.to_vec(),
            ));
        }

        // Validate the factory exists in the registry and the creation is within
        // the factory's declared constraints (program VK, capabilities, fields, mode, budget).
        //
        // For Derived/FromSet strategies, validate_and_record now checks that the
        // claimed program_vk is correctly derived or in the approved set.
        self.factory_registry
            .borrow_mut()
            .validate_and_record(factory_vk, params)
            .map_err(|e| {
                (
                    TurnError::InvalidEffect {
                        reason: format!("factory creation failed: {}", e),
                    },
                    path.to_vec(),
                )
            })?;

        // Determine the effective child VK to install.
        // For Derived strategy: compute the derived VK from factory_vk + params.
        // For FromSet strategy: use the claimed VK (already validated above).
        // For Fixed/None strategy: use params.program_vk as-is.
        let effective_vk = {
            let registry = self.factory_registry.borrow();
            let descriptor = registry.get(factory_vk);
            match descriptor.and_then(|d| d.child_vk_strategy.as_ref()) {
                Some(dregg_cell::factory::ChildVkStrategy::Derived { base_vk }) => {
                    let param_hash =
                        dregg_cell::factory::ChildVkStrategy::compute_param_hash(params);
                    Some(dregg_cell::factory::ChildVkStrategy::derive_child_vk(
                        base_vk,
                        &param_hash,
                    ))
                }
                Some(dregg_cell::factory::ChildVkStrategy::FromSet { .. }) => {
                    // Already validated; use the claimed VK.
                    params.program_vk
                }
                Some(dregg_cell::factory::ChildVkStrategy::Fixed(vk)) => *vk,
                None => params.program_vk,
            }
        };

        // Create the cell.
        let new_cell_id = CellId::derive_raw(owner_pubkey, token_id);
        let mut new_cell = match params.mode {
            dregg_cell::CellMode::Hosted => Cell::new_hosted(*owner_pubkey, *token_id),
            dregg_cell::CellMode::Sovereign => Cell::new(*owner_pubkey, *token_id),
        };

        // Set initial fields.
        for (idx, val) in &params.initial_fields {
            let idx = *idx as usize;
            if idx < dregg_cell::state::STATE_SLOTS {
                // Zero-pad to 32 bytes.
                let mut field = [0u8; 32];
                field[..8].copy_from_slice(&val.to_le_bytes());
                new_cell.state.fields[idx] = field;
            }
        }

        // Install program VK — use effective_vk (which may be derived).
        if let Some(vk_hash) = &effective_vk {
            new_cell.verification_key = Some(dregg_cell::VerificationKey::from_parts(
                *vk_hash,
                vk_hash.to_vec(), // Minimal VK data — the hash IS the identifier
            ));
        }

        // Install the factory descriptor's perpetual slot caveats
        // (`state_constraints`) as the born cell's `CellProgram`. Without this
        // the descriptor's Lane-G caveats (WriteOnce / Monotonic / …) never
        // bite: `apply_create_cell_from_factory` previously installed only the
        // VK *identifier*, leaving `cell.program == CellProgram::None`, so the
        // executor's per-cell predicate gate (`execute_tree.rs`) skipped the
        // cell entirely. The state_constraints are exactly the predicate the
        // factory advertises; installing them here is what makes a
        // factory-born cell's gating actually enforce on every subsequent turn
        // that touches it (reject-on-violation / accept-on-conform).
        {
            let state_constraints = self
                .factory_registry
                .borrow()
                .get(factory_vk)
                .map(|d| d.state_constraints.clone())
                .unwrap_or_default();
            if !state_constraints.is_empty() {
                new_cell.program = dregg_cell::CellProgram::Predicate(state_constraints);
            }
        }

        // Grant initial capabilities.
        for cap_grant in &params.initial_caps {
            let target_id = match &cap_grant.target {
                dregg_cell::factory::CapTarget::SelfCell => new_cell_id,
                dregg_cell::factory::CapTarget::Specific(id) => *id,
                dregg_cell::factory::CapTarget::Any => {
                    // "Any" in a grant means self for initial caps.
                    new_cell_id
                }
            };
            new_cell
                .capabilities
                .grant(target_id, cap_grant.max_permissions.clone());
        }

        // Insert into ledger.
        ledger.insert_cell(new_cell).map_err(|_| {
            (
                TurnError::CellAlreadyExists { id: new_cell_id },
                path.to_vec(),
            )
        })?;
        journal.record_create_cell(new_cell_id);
        Ok(())
    }

    // ─── Queue Operations ─────────────────────────────────────────────

    // ─── CapTP runtime effects (Stage 7 / P1.A, P1.B) ─────────────
    //
    // Mirror the mutations that used to live at the wire layer
    // (`wire/src/server.rs` :2243-2350). The executor is now the
    // single source of truth for CapTP state transitions. The
    // wire layer constructs a Turn with these effects and runs
    // it through `TurnExecutor::execute`.
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::too_many_arguments)]
    fn apply_refusal(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        offered_action_commitment: &[u8; 32],
        refusal_reason: &crate::action::RefusalReason,
        proof_witness_index: u32,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // `Refusal` is the categorical dual of acting-effects: it
        // attests that the prover did *not* take a specific action
        // within some window (CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.3).
        //
        // On apply we:
        //   1. Resolve the carried non-action witness blob and
        //      assert it exists at `proof_witness_index`. The
        //      *content* of the witness is the app's choice
        //      (receipt-chain scan, bloom non-membership, custom
        //      AIR); the executor only confirms the bytes are
        //      present so downstream verifiers can re-execute.
        //      Future tightening: dispatch through the witnessed-
        //      predicate registry on a kind embedded in the
        //      refusal (today the offered_action_commitment +
        //      reason discriminant pin the binding; the witness
        //      verifier is registered out-of-band by the app).
        //   2. Bump the target cell's nonce so the refusal is
        //      ordered against other turns on the same cell
        //      (replay-safe).
        //   3. Record the refusal commitment + reason in the
        //      protocol-reserved EXT audit field
        //      (`REFUSAL_AUDIT_EXT_KEY >= STATE_SLOTS`, committed via
        //      `fields_root`) — a blake3 commitment of
        //      `(offered_action_commitment, reason_discriminant)`
        //      so light clients can detect a refusal without
        //      re-fetching the witness. Landing the audit in
        //      `fields_root` (NOT the user-addressable `fields[0..15]`
        //      block) MOVES `compute_authority_digest_felt` (which
        //      folds `fields_root`), so the rotated AFTER block's
        //      `record_digest` limb advances on a genuine refusal and
        //      the `refusalV3` record-pin BITES (the verifier anchors
        //      PI 38 to the trusted post-cell digest). This matches the
        //      Lean SPEC `TurnExecutorFull.refusalField` (the named
        //      `"refusal"` record slot lands in `fields_root`).
        //   4. NEVER mutate balance, capability set, or any user value
        //      slot (`fields[0..15]`). Refusal is structurally *only* a
        //      non-action attestation; permission/value mutations
        //      belong to other effect variants.
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetState,
                "Refusal",
                dregg_cell::EFFECT_REFUSAL,
                path,
            )?;
        }
        // Witness presence check. The app supplies the actual
        // verifier through the WitnessedPredicateRegistry; the
        // executor only confirms the index RESOLVES to a real
        // witness blob carried by the action.
        //
        // That resolution happens in the per-action witness-binding
        // pass in `execute_tree` (right after effect partitioning):
        // it has `action.witness_blobs` in scope, which this per-effect
        // apply path does not, and rejects an out-of-range index with
        // `TurnError::InvalidWitnessIndex` BEFORE any effect is applied.
        // So by the time we reach here the index is guaranteed in-range;
        // we do not re-thread the blobs through every apply_* arm.
        let _ = proof_witness_index;
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        // KERNEL ALIGNMENT (lifecycle liveness): `refusalA` routes to
        // `stateStep s refusalField actor cell` (`TurnExecutorFull.lean:2581`),
        // gating `cellLive cell` (Live-ONLY). A refusal recorded on a
        // Sealed/Destroyed cell returns `none`.
        if !c.is_live() {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!("Refusal target cell {cell} is not live (sealed/destroyed)"),
                },
                path.to_vec(),
            ));
        }
        // Bump nonce (orders the refusal with respect to other
        // turns on this cell).
        journal.record_set_nonce(*cell, c.state.nonce());
        if !c.state.increment_nonce() {
            return Err((TurnError::NonceOverflow { cell: *cell }, path.to_vec()));
        }
        // Compute audit commitment for slot[4]:
        //   blake3("dregg-refusal-audit-v1" ||
        //          offered_action_commitment ||
        //          reason_disc ||
        //          (optional reason_hash))
        let mut h = blake3::Hasher::new_derive_key("dregg-refusal-audit-v1");
        h.update(offered_action_commitment);
        match refusal_reason {
            crate::action::RefusalReason::Declined => h.update(&[0u8]),
            crate::action::RefusalReason::NoAuthority => h.update(&[1u8]),
            crate::action::RefusalReason::WindowExpired => h.update(&[2u8]),
            crate::action::RefusalReason::Custom { reason_hash } => {
                h.update(&[3u8]);
                h.update(reason_hash)
            }
        };
        let audit = *h.finalize().as_bytes();
        // The protocol-reserved EXT audit key (`>= STATE_SLOTS`) lands the commitment in the
        // committed `fields_map` / `fields_root` — folded by `compute_authority_digest_felt`, so the
        // refusal MOVES the record-digest limb (the `refusalV3` forcing gate). Journal the prior
        // ext-value (`None` if the key was absent) so rollback restores it exactly.
        let audit_key = dregg_cell::state::REFUSAL_AUDIT_EXT_KEY;
        let old_audit = c.state.get_field_ext(audit_key);
        journal.record_set_field(*cell, audit_key as usize, old_audit);
        c.state.set_field_ext(audit_key, audit);
        Ok(())
    }

    // ── Cell lifecycle effects (Silver-Vision lifecycle subset) ──
    //
    // Each effect dispatches to the cell-side primitive shipped in
    // commits 9d819ea3/c0496d79/136ef24f. The executor handles:
    //   * target == action_target consistency (cross-cell lifecycle
    //     mutation is rejected as a structural error),
    //   * journaling the old lifecycle/capability state for rollback,
    //   * mapping `LifecycleTransitionError` to `TurnError::InvalidEffect`
    //     so the existing rollback path catches the failure.
    fn apply_cell_seal(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        target: &CellId,
        reason: [u8; 32],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if target != action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "CellSeal target must match action target".into(),
                },
                path.to_vec(),
            ));
        }
        let c = ledger
            .get_mut(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        let old = c.lifecycle.clone();
        c.seal(reason, self.block_height).map_err(|e| {
            (
                TurnError::InvalidEffect {
                    reason: format!("CellSeal failed: {e}"),
                },
                path.to_vec(),
            )
        })?;
        journal.record_set_lifecycle(*target, old);
        Ok(())
    }

    fn apply_cell_unseal(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        target: &CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if target != action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "CellUnseal target must match action target".into(),
                },
                path.to_vec(),
            ));
        }
        let c = ledger
            .get_mut(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        let old = c.lifecycle.clone();
        c.unseal().map_err(|e| {
            (
                TurnError::InvalidEffect {
                    reason: format!("CellUnseal failed: {e}"),
                },
                path.to_vec(),
            )
        })?;
        journal.record_set_lifecycle(*target, old);
        Ok(())
    }

    fn apply_cell_destroy(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        target: &CellId,
        certificate: &DeathCertificate,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if target != action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "CellDestroy target must match action target".into(),
                },
                path.to_vec(),
            ));
        }
        let c = ledger
            .get_mut(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        let old = c.lifecycle.clone();
        c.destroy(certificate).map_err(|e| {
            (
                TurnError::InvalidEffect {
                    reason: format!("CellDestroy failed: {e}"),
                },
                path.to_vec(),
            )
        })?;
        journal.record_set_lifecycle(*target, old);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_burn(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        _action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
        target: &CellId,
        slot: u32,
        amount: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Silver-Vision: only the canonical balance slot (sentinel
        // 0) is burnable. Future expansion may introduce per-asset
        // slots; for now any other slot is rejected so the executor
        // never silently writes outside the balance field.
        if slot != 0 {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "Burn slot {} is not a burnable balance slot (only slot 0 supported)",
                        slot
                    ),
                },
                path.to_vec(),
            ));
        }
        // KERNEL ALIGNMENT (supply-model Stage 3): burning is holder→well. A holder
        // reducing its OWN balance (`actor == target`) is permissionless self-redeem;
        // burning ANOTHER cell's balance requires authority over that holding. Burn has
        // NO action-level permission (`determine_required_permissions` has no Burn arm),
        // and the old guard was `target != action_target` — so `actor != target ==
        // action_target` (an agent targeting a victim) destroyed the victim's balance
        // with ZERO authority. Gate on `actor != target` instead, matching the verified
        // kernel's `actor = cell ∨ <authority>` (Dregg2.Exec recKBurnAsset, Stage 3).
        if actor != target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                target,
                dregg_cell::permissions::Action::Send,
                "Burn",
                dregg_cell::EFFECT_BURN,
                path,
            )?;
        }
        // SUPPLY-MODEL Stage 1 ("burn as issuer-move", the Lean `burnA`
        // dispatch): resolve the target asset's ISSUER WELL before mutating.
        // EVERY asset resolves a well now (registered override, else the
        // deterministic lazily-derived per-asset well — `derive_issuer_well`),
        // so burn is ALWAYS a conserving MOVE target→well: the well (carrying
        // −supply) is credited toward zero, holder debit == well credit, and
        // the verb conserves exactly (per-turn Σδ=0). The bare non-conserving
        // debit path is retired.
        //
        // HONEST SCOPE (docs/SUPPLY-MODEL.md): Stage 1 delivers PER-TURN
        // conservation (each burn nets zero). The STANDING invariant
        // `Σholders + well = 0` (the well as a proper −supply account) requires
        // wells to be initialized to −supply at issuance — that is Stage 2
        // (`Effect::Mint`). A lazily-created well starts at 0, so it goes
        // POSITIVE here (it accumulates burned value), not negative; the
        // per-turn delta is still exactly zero. Self-burn stays permissionless
        // (no mint-auth gate — that is Stage 3).
        let token_id = match ledger.get(target) {
            Some(c) => *c.token_id(),
            None => return Err((TurnError::CellNotFound { id: *target }, path.to_vec())),
        };
        let well_id = self
            .issuer_well_for(ledger, target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;

        let cm = ledger
            .get_mut(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        let bal = cm.state.balance();
        // Ordinary debit: you cannot burn more than you hold (floor zero).
        if !cm.state.debit_balance(amount) {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *target,
                    required: amount,
                    available: bal,
                },
                path.to_vec(),
            ));
        }
        journal.record_set_balance(*target, bal);

        {
            // Lazily materialize the well cell if it is absent (the common case
            // for any non-default asset, whose well is derived not registered).
            // The created well is a real signed, negative-capable cell in the
            // target's asset class; its creation is journaled so a later effect
            // failure rolls it back (the cell is removed).
            if !ledger.contains(&well_id) {
                let (well_pubkey, derived_id) = Self::derive_issuer_well(&token_id);
                // The well id must be the content-addressed id of the cell we
                // create — guaranteed because `issuer_well_for` derived it the
                // same way for an unregistered asset. A registered (override)
                // well, by contract, is created by whoever registered it
                // (genesis); if such a registered well is somehow absent we
                // still create a derived cell at `well_id`, but its id would
                // then mismatch its pre-image. Guard against that: only lazily
                // create when the resolved id equals the derived id.
                if well_id != derived_id {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: format!(
                                "registered issuer well {well_id} for the burn target's \
                                 asset not found"
                            ),
                        },
                        path.to_vec(),
                    ));
                }
                let well_cell = Cell::with_balance(well_pubkey, token_id, 0);
                ledger.insert_cell(well_cell).map_err(|e| {
                    (
                        TurnError::InvalidEffect {
                            reason: format!("{e}"),
                        },
                        path.to_vec(),
                    )
                })?;
                journal.record_create_cell(well_id);
            }
            let well = ledger.get_mut(&well_id).ok_or_else(|| {
                // Should be unreachable after the lazy-create above, but a
                // registered-yet-absent well refuses the burn (the journaled
                // debit above is rolled back by the caller on this error).
                (
                    TurnError::InvalidEffect {
                        reason: format!(
                            "issuer well {well_id} for the burn target's asset not found"
                        ),
                    },
                    path.to_vec(),
                )
            })?;
            // KERNEL ALIGNMENT (lifecycle liveness): the verified `recKBurnAsset`
            // (`Dregg2.Exec.RecordKernel.lean:757`) gates the ISSUER WELL `a` on
            // `cellLifecycleLive k a` (Live-ONLY). The holder `cell`/`target` is
            // NOT liveness-gated in Lean (only membership + availability), so we
            // gate ONLY the well here. A Sealed/Destroyed well refuses the burn.
            if !well.is_live() {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "issuer well {well_id} for the burn target's asset is not live \
                             (sealed/destroyed)"
                        ),
                    },
                    path.to_vec(),
                ));
            }
            let well_bal = well.state.balance();
            if !well.state.credit_balance(amount) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!("issuer well {well_id} balance overflow on burn credit"),
                    },
                    path.to_vec(),
                ));
            }
            journal.record_set_balance(well_id, well_bal);
        }
        Ok(())
    }

    /// Whether `actor` holds MINT authority over the issuer `well` — the Rust
    /// image of Lean `mintAuthorizedB` (`Generators.lean:36`). Mint authority is
    /// a CONTROL-GRADE capability over the issuer cell (the well) carrying the
    /// `EFFECT_MINT` facet, NOT bare ownership: a cell cannot coin its own
    /// supply, so `actor == well` is deliberately INSUFFICIENT (Lean rejects the
    /// self-cap likewise — the gate is a node/control cap on the issuer, which a
    /// cell does not implicitly hold over itself for this verb).
    ///
    /// Concretely: the actor must hold a non-revoked, non-expired cap targeting
    /// the well that BOTH (a) carries the `EFFECT_MINT` facet (its
    /// `allowed_effects` permits `EFFECT_MINT`), AND (b) is CONTROL-GRADE — the
    /// cap's own `permissions` are `AuthRequired::None` (a full, unencumbered
    /// control cap, the node-cap analog the `SetVerificationKey` surface rides;
    /// an attenuated `Signature`/`Proof`/`Impossible` cap is NOT control-grade
    /// for this gate). A cap that does not carry the `EFFECT_MINT` facet (e.g. a
    /// plain transfer/state cap) does NOT authorize minting.
    ///
    /// DECISION A (`docs/SUPPLY-MODEL.md`): this gates on the ACTOR's cap over
    /// the issuer, not the well's own permission table — matching Lean, where
    /// the authority is a cap the actor HOLDS, never a property of the issuer.
    fn holds_mint_authority(&self, ledger: &Ledger, actor: &CellId, well: &CellId) -> bool {
        // Bare ownership is NOT mint authority (Lean: no self-coin).
        if actor == well {
            return false;
        }
        let Some(actor_cell) = ledger.get(actor) else {
            return false;
        };
        let height = self.block_height;
        actor_cell
            .capabilities
            .capabilities_for(well)
            .into_iter()
            .chain(
                actor_cell
                    .delegation
                    .as_ref()
                    .into_iter()
                    .flat_map(|d| d.capabilities_for(well)),
            )
            .any(|c| {
                // (b) CONTROL-GRADE: a full open cap (the node-cap analog),
                // not an attenuated weaker grant.
                c.permissions == dregg_cell::AuthRequired::None
                    && c.expires_at.map_or(true, |exp| height <= exp)
                    // (a) the EFFECT_MINT facet.
                    && dregg_cell::is_effect_permitted(c.allowed_effects, dregg_cell::EFFECT_MINT)
            })
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn apply_mint(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        actor: &CellId,
        journal: &mut LedgerJournal,
        target: &CellId,
        slot: u32,
        amount: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // The sign-flipped DUAL of `apply_burn` (`docs/SUPPLY-MODEL.md` Stage
        // 2a): well → holder. The well (carrying −supply) is DEBITED negative-
        // capably (going more negative), the recipient `target` is CREDITED, and
        // the verb conserves exactly (per-turn, per-asset Σδ=0). The one place
        // mint ≠ burn is the AUTHORITY GATE: minting requires a control-grade
        // mint-cap over the issuer well, the Rust image of Lean `mintAuthorizedB`
        // (issuer authority, never bare ownership).

        // Slot guard: only the canonical balance slot (sentinel 0), exactly as
        // burn.
        if slot != 0 {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "Mint slot {} is not a mintable balance slot (only slot 0 supported)",
                        slot
                    ),
                },
                path.to_vec(),
            ));
        }

        // Resolve the target asset's ISSUER WELL (from `target`'s token_id, NOT
        // a field — same resolution as burn).
        let token_id = match ledger.get(target) {
            Some(c) => *c.token_id(),
            None => return Err((TurnError::CellNotFound { id: *target }, path.to_vec())),
        };
        let well_id = self
            .issuer_well_for(ledger, target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;

        // DISTINCTNESS (Lean `issuerOf a ≠ dst`): the well cannot be its own
        // recipient — a well→well "mint" is rejected.
        if well_id == *target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "Mint target must not be the asset's own issuer well".into(),
                },
                path.to_vec(),
            ));
        }
        // SELF-MINT (Lean: a cell cannot coin its own supply): the actor minting
        // INTO itself, or the actor being the well, is rejected. `actor == well`
        // is also caught by `holds_mint_authority`, but reject early for a clear
        // diagnostic.
        if actor == target || actor == &well_id {
            return Err((
                TurnError::InvalidEffect {
                    reason: "Mint is privileged: a cell cannot mint its own supply (self-mint \
                             rejected — mint authority is a cap over the issuer, not ownership)"
                        .into(),
                },
                path.to_vec(),
            ));
        }

        // Lazily materialize the well if absent — journaled, rollback-safe;
        // identical to burn's lazy-create (the derived id must match).
        if !ledger.contains(&well_id) {
            let (well_pubkey, derived_id) = Self::derive_issuer_well(&token_id);
            if well_id != derived_id {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "registered issuer well {well_id} for the mint target's asset not found"
                        ),
                    },
                    path.to_vec(),
                ));
            }
            let well_cell = Cell::with_balance(well_pubkey, token_id, 0);
            ledger.insert_cell(well_cell).map_err(|e| {
                (
                    TurnError::InvalidEffect {
                        reason: format!("{e}"),
                    },
                    path.to_vec(),
                )
            })?;
            journal.record_create_cell(well_id);
        }

        // AUTHORITY GATE (the one place mint ≠ burn): the actor must hold a
        // control-grade mint-cap over the well. Checked AFTER lazy-create so the
        // well's control permission can be read. Fail-closed.
        if !self.holds_mint_authority(ledger, actor, &well_id) {
            return Err((
                TurnError::CapabilityNotHeld {
                    actor: *actor,
                    target: well_id,
                },
                path.to_vec(),
            ));
        }

        // RECIPIENT LIVENESS (Lean `mintH` gates `acceptsEffects k cell` — Live-
        // ONLY; STRICTER than burn, which does not liveness-gate the holder).
        // Read it before mutating; a mint into a non-Live recipient is rejected.
        {
            let recip = ledger
                .get(target)
                .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
            if !recip.is_live() {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "Mint recipient cell {target} is not live (sealed/destroyed)"
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }

        // WELL LIVENESS (Lean `cellLifecycleLive k (issuerOf a)`): a
        // Sealed/Destroyed well refuses the mint. Read before mutating.
        {
            let well = ledger.get(&well_id).ok_or_else(|| {
                (
                    TurnError::InvalidEffect {
                        reason: format!(
                            "issuer well {well_id} for the mint target's asset not found"
                        ),
                    },
                    path.to_vec(),
                )
            })?;
            if !well.is_live() {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "issuer well {well_id} for the mint target's asset is not live \
                             (sealed/destroyed)"
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }

        // The CONSERVING move: debit the well (NEGATIVE-CAPABLE — the well
        // carries −supply and goes MORE negative as supply enters), credit the
        // holder. Both journaled; the per-turn delta nets to zero within the
        // asset.
        {
            let well = ledger
                .get_mut(&well_id)
                .ok_or_else(|| (TurnError::CellNotFound { id: well_id }, path.to_vec()))?;
            let well_bal = well.state.balance();
            // `well_debit_balance` is the issuer-well verb that MAY go negative
            // (vs the ordinary floor-at-zero `debit_balance`); fails only on i64
            // overflow.
            if !well.state.well_debit_balance(amount) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!("issuer well {well_id} balance underflow on mint debit"),
                    },
                    path.to_vec(),
                ));
            }
            journal.record_set_balance(well_id, well_bal);
        }
        {
            let recip = ledger
                .get_mut(target)
                .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
            let recip_bal = recip.state.balance();
            if !recip.state.credit_balance(amount) {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!("mint recipient {target} balance overflow on credit"),
                    },
                    path.to_vec(),
                ));
            }
            journal.record_set_balance(*target, recip_bal);
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_attenuate_capability(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        actor: &CellId,
        journal: &mut LedgerJournal,
        cell: &CellId,
        slot: u32,
        narrower_permissions: &dregg_cell::AuthRequired,
        narrower_effects: Option<u32>,
        narrower_expiry: Option<u64>,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if cell != actor {
            return Err((
                TurnError::InvalidEffect {
                    reason: "AttenuateCapability cell must match the actor".into(),
                },
                path.to_vec(),
            ));
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        // Snapshot the slot's prior fields for rollback BEFORE
        // attenuation.
        let prior = c
            .capabilities
            .iter()
            .find(|r| r.slot == slot)
            .ok_or_else(|| {
                (
                    TurnError::InvalidEffect {
                        reason: format!("AttenuateCapability slot {slot} not present in c-list"),
                    },
                    path.to_vec(),
                )
            })?;
        let old_permissions = prior.permissions.clone();
        let old_allowed_effects = prior.allowed_effects;
        let old_expires_at = prior.expires_at;
        let result = c.capabilities.attenuate_in_place(
            slot,
            narrower_permissions.clone(),
            narrower_effects,
            narrower_expiry,
        );
        if result.is_none() {
            return Err((
                TurnError::InvalidEffect {
                    reason: "AttenuateCapability rejected: not a monotone narrowing".into(),
                },
                path.to_vec(),
            ));
        }
        journal.record_attenuate_capability(
            *cell,
            slot,
            old_permissions,
            old_allowed_effects,
            old_expires_at,
        );
        Ok(())
    }

    fn apply_receipt_archive(
        &self,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        journal: &mut LedgerJournal,
        prefix_end_height: u64,
        checkpoint: &ArchivalAttestation,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if checkpoint.cell_id != *action_target {
            return Err((
                TurnError::InvalidEffect {
                    reason: "ReceiptArchive checkpoint cell_id mismatches action target".into(),
                },
                path.to_vec(),
            ));
        }
        if checkpoint.archive_end_height != prefix_end_height {
            return Err((
                TurnError::InvalidEffect {
                    reason:
                        "ReceiptArchive prefix_end_height mismatches checkpoint.archive_end_height"
                            .into(),
                },
                path.to_vec(),
            ));
        }
        // Reject archiving past the current head (block_height).
        if prefix_end_height > self.block_height {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "ReceiptArchive prefix_end_height {} exceeds current head height {}",
                        prefix_end_height, self.block_height
                    ),
                },
                path.to_vec(),
            ));
        }
        // Audit P0 #79: bind `archive_terminal_receipt_hash` to the
        // live chain head. Without this check, an attestation can
        // self-assert a fictional terminal receipt hash that bears
        // no relation to the actual chain, defeating the whole
        // point of the archive checkpoint (which is to pin the
        // chain at `archive_end_height` so post-archive turns can
        // link to it via `previous_receipt_hash`).
        //
        // The executor tracks `last_receipt_hash` per cell; for an
        // archive at height H, the terminal receipt hash MUST equal
        // the cell's currently-known chain head. (We do not store a
        // height->hash index here, so the strongest binding
        // available is "matches the most recent receipt the
        // executor has committed for this cell". A divergent claim
        // is rejected.) Cells with no prior receipt skip the check
        // — there is no head to bind to, and the attestation's own
        // non-zero invariant covers the degenerate case.
        if let Some(live_head) = self.get_last_receipt_hash(action_target) {
            if checkpoint.archive_terminal_receipt_hash != live_head {
                return Err((
                    TurnError::InvalidEffect {
                        reason: format!(
                            "ReceiptArchive archive_terminal_receipt_hash \
                             {:02x}{:02x}.. does not match live chain head \
                             {:02x}{:02x}.. for cell {:?}",
                            checkpoint.archive_terminal_receipt_hash[0],
                            checkpoint.archive_terminal_receipt_hash[1],
                            live_head[0],
                            live_head[1],
                            action_target,
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }
        let c = ledger.get_mut(action_target).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *action_target },
                path.to_vec(),
            )
        })?;
        // KERNEL ALIGNMENT: Lean's `receiptArchiveChainA` gates `cellLive` (Live-only,
        // `TurnExecutorFull.lean:1870`) — a Sealed/Destroyed/already-Archived cell cannot
        // be (re-)archived. Rust skipped this `is_live()` leg that every other lifecycle
        // arm carries; adding it also makes `Cell::archive`'s monotone Archived→Archived
        // path kernel-inaccessible (exercised by no flow — only the primitive's own unit
        // test), restoring consistency with the verified spec + the sibling effect arms.
        if !c.is_live() {
            return Err((
                TurnError::InvalidEffect {
                    reason: format!(
                        "ReceiptArchive on a non-Live cell {action_target:?} (lifecycle must be Live)"
                    ),
                },
                path.to_vec(),
            ));
        }
        let old = c.lifecycle.clone();
        c.archive(checkpoint).map_err(|e| {
            (
                TurnError::InvalidEffect {
                    reason: format!("ReceiptArchive failed: {e}"),
                },
                path.to_vec(),
            )
        })?;
        journal.record_set_lifecycle(*action_target, old);
        Ok(())
    }

    // ─── Shared helpers ──────────────────────────────────────────────────────

    /// Height-aware check: does the cell have a non-expired capability to the target?
    ///
    /// Uses `has_access_at` to filter out capabilities whose `expires_at` has passed.
    pub(super) fn has_access_including_delegation_at(
        cell: &Cell,
        target: &CellId,
        current_height: u64,
    ) -> bool {
        // A cell implicitly holds the strongest capability over itself. The
        // alternative — requiring an explicit c-list entry to one's own id —
        // forces every newly-created cell to insert a self-grant before it
        // can be bound into a bearer cap. Treat self-access as inherent.
        if cell.id() == *target {
            return true;
        }
        // Direct capability (height-aware)
        if cell.capabilities.has_access_at(target, current_height) {
            return true;
        }
        // Delegated capability (from snapshot)
        if let Some(ref delegation) = cell.delegation {
            if delegation.has_capability(target) {
                return true;
            }
        }
        false
    }

    /// FACET-aware sibling of [`has_access_including_delegation_at`]: the actor
    /// must hold a path to `target` whose `allowed_effects` mask ADMITS the
    /// effect-kind being attempted (`effect_bit`), not merely a path that
    /// exists. This is the direct cross-cell facet leg the verified kernel's
    /// `authorizedB` enforces (`metatheory/Dregg2/Exec/Kernel.lean:54` — an
    /// `.endpoint` cap is authorized only when its `rights` carry the required
    /// facet). Presence is gated separately by `has_access_including_delegation_at`
    /// so that "no cap at all" stays a `CapabilityNotHeld` while "cap present but
    /// faceted away" becomes a `FacetViolation`, matching the
    /// `ExerciseViaCapability` sibling (`apply.rs:1803`). `CAP-FACET-1`.
    pub(super) fn permits_effect_including_delegation_at(
        cell: &Cell,
        target: &CellId,
        current_height: u64,
        effect_bit: dregg_cell::EffectMask,
    ) -> bool {
        // A cell implicitly holds the full-facet capability over itself
        // (`actor == src` in `authorizedB`): no facet restricts an owner.
        if cell.id() == *target {
            return true;
        }
        // Direct capability, facet-checked.
        if cell
            .capabilities
            .permits_effect_at(target, current_height, effect_bit)
        {
            return true;
        }
        // Delegated capability (from snapshot), facet-checked. Mirrors the
        // presence semantics of the delegation branch above (target match,
        // non-revoked) plus the facet admission.
        if let Some(ref delegation) = cell.delegation {
            if delegation.capabilities_for(target).iter().any(|cap| {
                cap.permissions != dregg_cell::AuthRequired::Impossible
                    && dregg_cell::is_effect_permitted(cap.allowed_effects, effect_bit)
            }) {
                return true;
            }
        }
        false
    }

    /// Walk the delegation chain from `start_cell` upward (via `cell.delegate`)
    /// looking for an ancestor that holds a capability to `target`.
    ///
    /// Returns `Some(ancestor_id)` if an ancestor with the capability is found,
    /// `None` otherwise. Limits the walk to 16 hops to prevent infinite loops.
    pub(super) fn walk_delegation_chain_for_capability(
        ledger: &Ledger,
        start_cell: &CellId,
        target: &CellId,
        current_height: u64,
    ) -> Option<CellId> {
        let mut current_id = *start_cell;
        let max_hops = 16;

        for _ in 0..max_hops {
            let cell = ledger.get(&current_id)?;
            // Check if this cell's delegate (parent) has the capability.
            let parent_id = cell.delegate?;
            let parent_cell = ledger.get(&parent_id)?;
            if Self::has_access_including_delegation_at(parent_cell, target, current_height) {
                return Some(parent_id);
            }
            current_id = parent_id;
        }

        None
    }

    /// SECURITY: Check that the actor holds a capability to the given cell AND that
    /// the cell's permission for the given action is not denied.
    pub(super) fn check_cross_cell_permission(
        &self,
        ledger: &Ledger,
        actor: &CellId,
        target_cell_id: &CellId,
        permission_action: dregg_cell::permissions::Action,
        action_name: &str,
        effect_bit: dregg_cell::EffectMask,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if actor != target_cell_id {
            let actor_cell = ledger
                .get(actor)
                .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
            if !Self::has_access_including_delegation_at(
                actor_cell,
                target_cell_id,
                self.block_height,
            ) {
                return Err((
                    TurnError::CapabilityNotHeld {
                        actor: *actor,
                        target: *target_cell_id,
                    },
                    path.to_vec(),
                ));
            }
            // CAP-FACET-1: presence is not authority. The held cap's
            // `allowed_effects` FACET must ADMIT the effect being attempted on
            // this direct cross-cell path — matching the `ExerciseViaCapability`
            // sibling (`apply.rs:1803`, routing through `is_effect_permitted`)
            // and the verified kernel's `authorizedB` (`Kernel.lean:54`), which
            // authorizes an `.endpoint` cap only when its rights carry the
            // required facet. Without this, a SetField-only faceted cap could
            // drive a `Transfer` against a `None`-permission target (Rust
            // commits, Lean rejects — a rejection-parity break + cap
            // amplification).
            if !Self::permits_effect_including_delegation_at(
                actor_cell,
                target_cell_id,
                self.block_height,
                effect_bit,
            ) {
                return Err((
                    TurnError::FacetViolation {
                        actor: *actor,
                        target: *target_cell_id,
                        // The direct path resolves authority across the whole
                        // c-list, not a single exercised slot; report 0.
                        cap_slot: 0,
                        attempted_effect: action_name.to_string(),
                        allowed_mask: actor_cell
                            .capabilities
                            .effect_mask_union_for(target_cell_id),
                    },
                    path.to_vec(),
                ));
            }
        }

        let cell = ledger.get(target_cell_id).ok_or_else(|| {
            (
                TurnError::CellNotFound {
                    id: *target_cell_id,
                },
                path.to_vec(),
            )
        })?;
        let required = cell.permissions.for_action(permission_action);
        if matches!(required, AuthRequired::Impossible) {
            return Err((
                TurnError::PermissionDenied {
                    cell: *target_cell_id,
                    action: action_name.to_string(),
                    required: required.clone(),
                },
                path.to_vec(),
            ));
        }
        if !matches!(required, AuthRequired::None) {
            return Err((
                TurnError::PermissionDenied {
                    cell: *target_cell_id,
                    action: action_name.to_string(),
                    required: required.clone(),
                },
                path.to_vec(),
            ));
        }

        Ok(())
    }
}

// ─── End-to-end React-through-the-executor forge-detector ────────────────────
//
// The Track-2 bar: a `React` effect driven through the executor's `apply_effect`
// dispatch resolves ONCE and SPENDS `pending_id` into the production
// `note_nullifiers` set; a SECOND react on the same hole id — or a replay of the
// same `pending_id` — is REJECTED by that identical nullifier gate (the same gate
// `NoteSpend` rides). Not a stub: the rejection is the genuine double-spend
// refusal from `NullifierSet::insert`, observed at the executor entry point.
#[cfg(test)]
mod react_executor_tests {
    use super::*;
    use crate::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
    use crate::conditional::{ConditionProof, ProofCondition};
    use crate::forest::CallForest;
    use crate::pending::ResolutionCondition;
    use crate::turn::Turn;
    use dregg_cell::{CellId, Nullifier, Preconditions};

    /// A minimal wake turn for `cell` (the turn the recipient runs on react).
    /// Its hash is the promise-hole id == the React nullifier.
    fn wake_turn(cell: CellId, nonce: u64) -> Turn {
        let action = Action {
            target: cell,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        Turn {
            agent: cell,
            nonce,
            call_forest: forest,
            fee: 1000,
            memo: None,
            valid_until: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            previous_receipt_hash: None,
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// A hash-preimage condition + its discharging proof — the simplest genuine
    /// wake/react pair (the reactor reveals the preimage the notify committed to).
    fn preimage_pair() -> (ProofCondition, ConditionProof) {
        let preimage = [0x5Au8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();
        (
            ProofCondition::HashPreimage { hash },
            ConditionProof::Preimage(preimage),
        )
    }

    /// Build a React effect whose `pending_id` is bound to `wake` (its hash).
    fn react_effect(wake: &Turn, condition: ProofCondition, proof: ConditionProof) -> Effect {
        Effect::React {
            pending_id: Nullifier(wake.hash()),
            condition,
            resolution_proof: proof,
            wake: Box::new(wake.clone()),
        }
    }

    fn react_cell() -> CellId {
        CellId::from_bytes([0xB0; 32])
    }

    // ── THE END-TO-END FORGE-DETECTOR: react once spends the nullifier; a
    //    SECOND react on the SAME hole id is REJECTED by the executor's
    //    note_nullifiers gate (the same double-spend gate NoteSpend rides). ──
    #[test]
    fn react_through_executor_spends_once_and_rejects_react_twice() {
        let executor = crate::executor::TurnExecutor::new(crate::executor::ComputronCosts::zero());
        let cell = react_cell();
        let wake = wake_turn(cell, 0);
        let pending_id = Nullifier(wake.hash());
        let (condition, proof) = preimage_pair();

        // First, NOTIFY: deposit the hole in the executor's reactive registry
        // (the recipient's wake). This is the genuine standing commitment.
        let notify = Effect::Notify {
            from: cell,
            to: cell,
            wake: Box::new(wake.clone()),
            resolution_condition: ResolutionCondition::AwaitCondition(condition.clone()),
            timeout_height: 100,
        };
        let mut ledger = Ledger::new();
        let mut journal = LedgerJournal::new();
        executor
            .apply_effect(&notify, &mut ledger, &[0], &cell, &cell, &mut journal)
            .expect("notify deposits the hole");
        assert_eq!(
            executor.reactive_registry.lock().unwrap().len(),
            1,
            "one live hole after notify"
        );
        assert!(
            !executor
                .note_nullifiers
                .lock()
                .unwrap()
                .contains(&pending_id),
            "hole id not yet spent"
        );

        // FIRST REACT: resolves and SPENDS the pending_id nullifier.
        let react = react_effect(&wake, condition.clone(), proof.clone());
        let mut journal1 = LedgerJournal::new();
        executor
            .apply_effect(&react, &mut ledger, &[1], &cell, &cell, &mut journal1)
            .expect("a genuine react resolves once");
        assert!(
            executor
                .note_nullifiers
                .lock()
                .unwrap()
                .contains(&pending_id),
            "the hole id is now SPENT in the production nullifier set (the grow-gate step)"
        );
        assert_eq!(
            executor.reactive_registry.lock().unwrap().len(),
            0,
            "the hole is consumed (registry removal — the redundant second tooth)"
        );

        // SECOND REACT on the SAME hole id: REJECTED by the nullifier gate.
        // This is the genuine double-spend refusal — NOT an unconditional Err:
        // the executor finds pending_id already in note_nullifiers and refuses.
        let mut journal2 = LedgerJournal::new();
        let twice = executor.apply_effect(&react, &mut ledger, &[2], &cell, &cell, &mut journal2);
        let (err, _) = twice.expect_err("react-twice MUST be rejected by the nullifier gate");
        match err {
            TurnError::InvalidEffect { reason } => assert!(
                reason.contains("double-spend") && reason.contains("one-shot"),
                "rejection must be the double-spend one-shot refusal, got: {reason}"
            ),
            other => panic!("expected InvalidEffect double-spend, got {other:?}"),
        }
        // The nullifier set still holds exactly the one spend.
        assert!(
            executor
                .note_nullifiers
                .lock()
                .unwrap()
                .contains(&pending_id)
        );
    }

    // ── A REPLAYED pending_id (a fresh React carrying the SAME hole id, even
    //    re-notified) is refused by the SAME gate — the one-shot is enforced at
    //    the nullifier layer, not merely by registry removal. ──
    #[test]
    fn replayed_pending_id_refused_by_nullifier_gate() {
        let executor = crate::executor::TurnExecutor::new(crate::executor::ComputronCosts::zero());
        let cell = react_cell();
        let wake = wake_turn(cell, 0);
        let pending_id = Nullifier(wake.hash());
        let (condition, proof) = preimage_pair();
        let mut ledger = Ledger::new();

        // React #1 — spends pending_id.
        let react = react_effect(&wake, condition.clone(), proof.clone());
        let mut j1 = LedgerJournal::new();
        executor
            .apply_effect(&react, &mut ledger, &[0], &cell, &cell, &mut j1)
            .expect("first react spends the hole id");
        assert!(
            executor
                .note_nullifiers
                .lock()
                .unwrap()
                .contains(&pending_id)
        );

        // RE-NOTIFY the same hole (a fresh live registry entry with the same id),
        // then REACT again. The registry-removal tooth is bypassed (the hole is
        // live again), but the nullifier gate still refuses: the hole id was
        // already spent.
        let notify = Effect::Notify {
            from: cell,
            to: cell,
            wake: Box::new(wake.clone()),
            resolution_condition: ResolutionCondition::AwaitCondition(condition.clone()),
            timeout_height: 100,
        };
        let mut jn = LedgerJournal::new();
        executor
            .apply_effect(&notify, &mut ledger, &[1], &cell, &cell, &mut jn)
            .expect("re-notify deposits a fresh live hole");
        assert_eq!(executor.reactive_registry.lock().unwrap().len(), 1);

        let mut j2 = LedgerJournal::new();
        let replay = executor.apply_effect(&react, &mut ledger, &[2], &cell, &cell, &mut j2);
        let (err, _) = replay.expect_err("a replayed pending_id MUST be refused");
        assert!(
            matches!(err, TurnError::InvalidEffect { reason } if reason.contains("double-spend")),
            "the replay is refused by the production nullifier gate (the hole id is spent)"
        );
    }

    // ── The nullifier↔turn binding is genuine: a React whose `wake` does NOT
    //    hash to `pending_id` is refused (it cannot spend one hole while
    //    claiming to resolve another). ──
    #[test]
    fn react_with_mismatched_wake_refused() {
        let executor = crate::executor::TurnExecutor::new(crate::executor::ComputronCosts::zero());
        let cell = react_cell();
        let wake = wake_turn(cell, 0);
        let other = wake_turn(cell, 999); // a DIFFERENT turn (different nonce)
        let (condition, proof) = preimage_pair();

        // pending_id claims `wake`, but the carried resolved turn is `other`.
        let forged = Effect::React {
            pending_id: Nullifier(wake.hash()),
            condition,
            resolution_proof: proof,
            wake: Box::new(other),
        };
        let mut ledger = Ledger::new();
        let mut journal = LedgerJournal::new();
        let r = executor.apply_effect(&forged, &mut ledger, &[0], &cell, &cell, &mut journal);
        let (err, _) = r.expect_err("a mismatched wake/pending_id MUST be refused");
        assert!(
            matches!(err, TurnError::InvalidEffect { reason } if reason.contains("binding")),
            "refusal must cite the nullifier↔turn binding violation"
        );
        // Nothing was spent — a refused react burns no hole.
        assert!(
            !executor
                .note_nullifiers
                .lock()
                .unwrap()
                .contains(&Nullifier(wake.hash())),
            "a refused react spends no nullifier"
        );
    }

    // ── A WRONG proof is refused and spends nothing (fail-closed): the hole id
    //    is NOT inserted into the nullifier set on a failed react. ──
    #[test]
    fn wrong_proof_refused_spends_nothing() {
        let executor = crate::executor::TurnExecutor::new(crate::executor::ComputronCosts::zero());
        let cell = react_cell();
        let wake = wake_turn(cell, 0);
        let pending_id = Nullifier(wake.hash());
        let (condition, _good) = preimage_pair();
        let wrong = ConditionProof::Preimage([0xFFu8; 32]); // not the preimage

        let react = react_effect(&wake, condition.clone(), wrong);
        let mut ledger = Ledger::new();
        let mut journal = LedgerJournal::new();
        let r = executor.apply_effect(&react, &mut ledger, &[0], &cell, &cell, &mut journal);
        assert!(
            matches!(r, Err((TurnError::InvalidEffect { .. }, _))),
            "a wrong proof is refused"
        );
        assert!(
            !executor
                .note_nullifiers
                .lock()
                .unwrap()
                .contains(&pending_id),
            "fail-closed: a refused react inserts no nullifier"
        );

        // The GENUINE proof can still discharge it afterwards (the bad attempt
        // did not poison the nullifier gate).
        let (cond2, good) = preimage_pair();
        let good_react = react_effect(&wake, cond2, good);
        let mut journal2 = LedgerJournal::new();
        executor
            .apply_effect(&good_react, &mut ledger, &[1], &cell, &cell, &mut journal2)
            .expect("the genuine proof discharges the hole");
        assert!(
            executor
                .note_nullifiers
                .lock()
                .unwrap()
                .contains(&pending_id)
        );
    }
}

/// A GENUINE resolution receipt for a discharged promise-hole: content-addressed
/// to the resolved `wake` turn (whose hash the React effect verified equals the
/// spent `pending_id`). Unlike a fabricated receipt, every field is derived from
/// the real resolved turn — `forest_hash` from its call forest, `post_state_hash`
/// bound to the turn hash — so the registry's cascade carries a real provenance
/// link to the turn that was actually proven-resolved.
fn genuine_resolution_receipt(wake: &Turn) -> TurnReceipt {
    let turn_hash = wake.hash();
    TurnReceipt {
        turn_hash,
        forest_hash: wake.call_forest.compute_hash(),
        pre_state_hash: [0u8; 32],
        post_state_hash: turn_hash,
        timestamp: 0i64,
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: wake.call_forest.roots.len(),
        previous_receipt_hash: None,
        agent: wake.agent,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: vec![],
    }
}

// ─── End-to-end shielded transfer through the executor (privacy M2-a) ─────────
//
// The bar: a `ShieldedTransfer` effect driven through the real `apply_effect`
// dispatch is ADMITTED when (and only when) its hidden STARK side, its Pedersen
// conservation+range side, and the nullifier gate all pass — and is REJECTED on a
// forged proof, a non-conserving value set, or a re-presented (double-spent)
// nullifier. Not a stub: each rejection is the genuine refusal from the real
// `dregg-circuit-prove` verifier / `dregg-cell-crypto` conservation verifier /
// `NullifierSet::insert`, observed at the executor entry point.
#[cfg(all(test, feature = "prover"))]
mod shielded_executor_tests {
    use super::*;
    use crate::action::{Effect, ShieldedInputPayload, ShieldedLeg, ShieldedTransferPayload};
    use dregg_cell_crypto::value_commitment::{
        BulletproofRangeProof, ValueCommitment, prove_conservation, scalar_from_blinding_bytes,
    };
    use dregg_circuit::field::BabyBear;
    use dregg_circuit_prove::shielded::{
        ShieldedSpendWitness, ShieldedTransfer, ShieldedTransferWitness, ShieldedValueLeg,
    };

    const ASSET: u64 = 1;

    fn range_proof_bytes(value: u64, blinding: &[u8; 32]) -> Vec<u8> {
        BulletproofRangeProof::prove_range(value, &scalar_from_blinding_bytes(blinding)).proof_bytes
    }

    /// A shielded-spend witness with a genuine Poseidon2 Merkle path + its leg.
    fn make_input(
        leaf_seed: u32,
        amount: u32,
        blinding: [u8; 32],
        key_seed: u32,
        depth: usize,
    ) -> ShieldedTransferWitness {
        let key = [
            BabyBear::new(key_seed),
            BabyBear::new(key_seed.wrapping_add(1)),
            BabyBear::new(key_seed.wrapping_add(2)),
            BabyBear::new(key_seed.wrapping_add(3)),
        ];
        let mut siblings = Vec::with_capacity(depth);
        let mut positions = Vec::with_capacity(depth);
        for i in 0..depth {
            positions.push((i % 4) as u8);
            siblings.push([
                BabyBear::new((i as u32) * 7 + 1 + leaf_seed),
                BabyBear::new((i as u32) * 7 + 2 + leaf_seed),
                BabyBear::new((i as u32) * 7 + 3 + leaf_seed),
            ]);
        }
        let spend = ShieldedSpendWitness {
            value: BabyBear::new(amount),
            asset_type: BabyBear::new(ASSET as u32),
            owner: BabyBear::new(0x5EED ^ leaf_seed),
            randomness: BabyBear::new(0xC0FFEE ^ key_seed),
            key,
            siblings,
            positions,
        };
        let commitment =
            ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&blinding));
        ShieldedTransferWitness {
            spend,
            leg: ShieldedValueLeg {
                asset_type: ASSET,
                commitment_bytes: commitment.to_bytes().0,
            },
        }
    }

    /// Serialize a built circuit `ShieldedTransfer` + its conservation proof into
    /// the executor wire payload — exactly what a client would post.
    fn to_payload(
        transfer: &ShieldedTransfer,
        conservation: dregg_cell_crypto::ConservationProof,
    ) -> ShieldedTransferPayload {
        let leg = |l: &ShieldedValueLeg| ShieldedLeg {
            asset_type: l.asset_type,
            commitment_bytes: l.commitment_bytes,
        };
        ShieldedTransferPayload {
            merkle_root: transfer.merkle_root.as_u32(),
            inputs: transfer
                .inputs
                .iter()
                .map(|ip| ShieldedInputPayload {
                    nullifier: ip.nullifier.as_u32(),
                    value_binding: ip.value_binding.as_u32(),
                    proof: ip.proof_bytes(),
                })
                .collect(),
            input_legs: transfer.input_legs.iter().map(leg).collect(),
            output_legs: transfer.output_legs.iter().map(leg).collect(),
            output_range_proofs: transfer.output_range_proofs.clone(),
            conservation,
        }
    }

    /// A balanced one-in/one-out shielded transfer + the matching payload.
    fn balanced_payload(leaf_seed: u32, key_seed: u32) -> ShieldedTransferPayload {
        let amount = 1_000_000u32;
        // Independent per-note blinding (derived from the seeds): the source of
        // value-commitment unlinkability — equal amounts still commit distinctly.
        let mut in_blinding = [3u8; 32];
        let mut out_blinding = [7u8; 32];
        in_blinding[..4].copy_from_slice(&leaf_seed.to_le_bytes());
        out_blinding[..4].copy_from_slice(&key_seed.to_le_bytes());
        let w = make_input(leaf_seed, amount, in_blinding, key_seed, 4);
        let merkle_root = w.spend.merkle_root();
        let in_c =
            ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&in_blinding));
        let out_c =
            ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&out_blinding));
        let output_legs = vec![ShieldedValueLeg {
            asset_type: ASSET,
            commitment_bytes: out_c.to_bytes().0,
        }];
        let output_range_proofs = vec![range_proof_bytes(amount as u64, &out_blinding)];
        let transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
            merkle_root,
            &[w],
            output_legs,
            output_range_proofs,
        )
        .expect("prove balanced shielded transfer");
        let excess =
            scalar_from_blinding_bytes(&in_blinding) - scalar_from_blinding_bytes(&out_blinding);
        let msg = transfer.transfer_message();
        let conservation = prove_conservation(&[in_c], &[out_c], &excess, &msg);
        to_payload(&transfer, conservation)
    }

    fn run(
        executor: &crate::executor::TurnExecutor,
        payload: ShieldedTransferPayload,
        path_idx: usize,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let cell = CellId::from_bytes([0x5A; 32]);
        let effect = Effect::ShieldedTransfer { payload };
        let mut ledger = Ledger::new();
        let mut journal = LedgerJournal::new();
        executor.apply_effect(
            &effect,
            &mut ledger,
            &[path_idx],
            &cell,
            &cell,
            &mut journal,
        )
    }

    // ── ACCEPT: a balanced, in-range, well-formed shielded transfer is admitted,
    //    and its nullifier is now spent in the production set. ──
    #[test]
    fn valid_shielded_transfer_is_admitted_and_spends_its_nullifier() {
        let executor = crate::executor::TurnExecutor::new(crate::executor::ComputronCosts::zero());
        let payload = balanced_payload(11, 0xABCD);
        let nf = shielded_nullifier_key(payload.inputs[0].nullifier);
        assert!(!executor.note_nullifiers.lock().unwrap().contains(&nf));
        run(&executor, payload, 0).expect("a valid shielded transfer must be admitted");
        assert!(
            executor.note_nullifiers.lock().unwrap().contains(&nf),
            "the shielded input's nullifier is now spent in the production set"
        );
    }

    // ── REJECT (forged membership): a tampered merkle_root breaks the hidden
    //    STARK side — no fake membership. ──
    #[test]
    fn forged_membership_root_rejects() {
        let executor = crate::executor::TurnExecutor::new(crate::executor::ComputronCosts::zero());
        let mut payload = balanced_payload(12, 0xBEEF);
        payload.merkle_root = payload.merkle_root.wrapping_add(1);
        let (err, _) = run(&executor, payload, 0).expect_err("forged root must reject");
        match err {
            TurnError::InvalidEffect { reason } => {
                assert!(reason.contains("STARK"), "got: {reason}")
            }
            other => panic!("expected InvalidEffect STARK, got {other:?}"),
        }
    }

    // ── REJECT (no double-spend): the SAME shielded transfer presented twice is
    //    refused by the nullifier gate — the genuine double-spend refusal. ──
    #[test]
    fn double_spent_shielded_nullifier_rejects() {
        let executor = crate::executor::TurnExecutor::new(crate::executor::ComputronCosts::zero());
        let payload = balanced_payload(13, 0xF00D);
        run(&executor, payload.clone(), 0).expect("first shielded transfer admitted");
        let (err, _) = run(&executor, payload, 1).expect_err("second presentation must reject");
        match err {
            TurnError::InvalidEffect { reason } => assert!(
                reason.contains("double-spend"),
                "rejection must be the double-spend refusal, got: {reason}"
            ),
            other => panic!("expected InvalidEffect double-spend, got {other:?}"),
        }
    }

    // ── REJECT (non-conserving): an output committing to MORE than the input
    //    (hidden inflation) fails the Pedersen conservation gate — even though the
    //    STARK membership is genuine. Σδ ≠ 0 ⇒ refused. ──
    #[test]
    fn inflating_shielded_transfer_rejects_on_conservation() {
        let executor = crate::executor::TurnExecutor::new(crate::executor::ComputronCosts::zero());
        let amount = 1_000_000u32;
        let inflated = 2_000_000u64;
        let in_blinding = [3u8; 32];
        let out_blinding = [7u8; 32];
        let w = make_input(14, amount, in_blinding, 0x1234, 4);
        let merkle_root = w.spend.merkle_root();
        let in_c =
            ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&in_blinding));
        // The output leg commits to the INFLATED value (a real, in-range value, so
        // its range proof is valid) — only conservation can catch this.
        let out_c = ValueCommitment::commit(inflated, &scalar_from_blinding_bytes(&out_blinding));
        let output_legs = vec![ShieldedValueLeg {
            asset_type: ASSET,
            commitment_bytes: out_c.to_bytes().0,
        }];
        let output_range_proofs = vec![range_proof_bytes(inflated, &out_blinding)];
        let transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
            merkle_root,
            &[w],
            output_legs,
            output_range_proofs,
        )
        .expect("STARK builds even for an inflating transfer (caught at conservation)");
        // The prover still uses the blinding excess; the value imbalance makes the
        // excess carry a V-component, so the Schnorr-on-R proof cannot answer.
        let excess =
            scalar_from_blinding_bytes(&in_blinding) - scalar_from_blinding_bytes(&out_blinding);
        let msg = transfer.transfer_message();
        let conservation = prove_conservation(&[in_c], &[out_c], &excess, &msg);
        let payload = to_payload(&transfer, conservation);
        let (err, _) =
            run(&executor, payload, 0).expect_err("an inflating shielded transfer must reject");
        match err {
            TurnError::InvalidEffect { reason } => assert!(
                reason.contains("conservation") || reason.contains("range"),
                "rejection must be the value-conservation gate, got: {reason}"
            ),
            other => panic!("expected InvalidEffect conservation, got {other:?}"),
        }
        // Nothing was spent — the transfer was refused before the nullifier gate
        // could record (the conservation gate precedes the spend).
        assert!(executor.note_nullifiers.lock().unwrap().is_empty());
    }

    // ── UNLINKABILITY: two independent shielded transfers of the SAME amount
    //    produce DIFFERENT nullifiers / commitments / proofs — an observer cannot
    //    link sender to receiver by the on-wire payload. ──
    #[test]
    fn distinct_transfers_are_unlinkable_on_the_wire() {
        let a = balanced_payload(21, 0x1111);
        let b = balanced_payload(22, 0x2222);
        assert_ne!(
            a.inputs[0].nullifier, b.inputs[0].nullifier,
            "distinct shielded inputs must reveal distinct nullifiers"
        );
        assert_ne!(
            a.output_legs[0].commitment_bytes, b.output_legs[0].commitment_bytes,
            "equal amounts must still commit to distinct (blinded) value commitments"
        );
        assert_ne!(
            a.inputs[0].proof, b.inputs[0].proof,
            "the hidden proofs reveal nothing linking the two transfers"
        );
    }
}

// ─── Note-spend BridgeMint verify: the StarkProof → Ir2BatchProof wire flip ──
//
// Round-trips a REAL note-spend witness (spending key + 28-limb note commitment
// + Merkle path) through the committed IR-v2 descriptor prover
// (`note_spend_witness` → `prove_vm_descriptor2` → `postcard`) and back through
// the executor's BridgeMint consumer leg (`verify_note_spend_descriptor2` →
// `verify_vm_descriptor2` over the FAIL-CLOSED `note-spend-leaf` descriptor).
// The honest proof is ACCEPTED (so the accept is non-vacuous); every tampered
// PI claim and every corrupted/empty blob is REJECTED (so the descriptor's
// boundary pins are load-bearing — the four bridge trapdoors stay closed).
#[cfg(test)]
mod note_spend_descriptor_flip_tests {
    use dregg_circuit::BabyBear;
    use dregg_circuit::descriptor_by_name::descriptor_by_name;
    use dregg_circuit::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2};
    use dregg_circuit::dsl::note_spending::note_spend_mint_hash_felt;
    use dregg_circuit::note_spend_witness::{NOTE_SPEND_LEAF_NAME, note_spend_witness};
    use dregg_circuit::note_spending_air::{NoteSpendingWitness, test_spending_key};
    use dregg_circuit::poseidon2::hash_many;

    /// A REAL full-width note-spend witness — depth-2 Merkle path, a value above
    /// 2^30 so the high limb is live. Mirrors the shape the circuit crate's own
    /// `note_spend_witness` tests use.
    fn make_witness(tag: u8) -> NoteSpendingWitness {
        let owner = [tag; 32];
        let nonce = [tag ^ 0x5A; 32];
        let rand = [tag ^ 0xA5; 32];
        let key = test_spending_key(tag as u32 + 0x77);
        let depth = 2usize;
        let mut siblings = Vec::with_capacity(depth);
        let mut positions = Vec::with_capacity(depth);
        for i in 0..depth {
            siblings.push([
                hash_many(&[BabyBear::new((i * 3 + 1) as u32), BabyBear::new(tag as u32)]),
                hash_many(&[BabyBear::new((i * 3 + 2) as u32), BabyBear::new(tag as u32)]),
                hash_many(&[BabyBear::new((i * 3 + 3) as u32), BabyBear::new(tag as u32)]),
            ]);
            positions.push((i % 4) as u8);
        }
        NoteSpendingWitness::from_note_limbs(
            &owner,
            0xDEAD_BEEF_CAFE, // > 2^30: the value_hi limb is live
            3,
            &nonce,
            &rand,
            key,
            siblings,
            positions,
        )
    }

    /// Prove a real note-spend through the emitted descriptor and postcard-encode
    /// it (the producer half, exactly what the SDK/bridge does). Returns the
    /// witness's 7-slot PI vector and the wire blob.
    fn prove_blob(w: &NoteSpendingWitness) -> (Vec<BabyBear>, Vec<u8>) {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("note-spend leaf dispatches");
        let (trace, pis) = note_spend_witness(w).expect("witness builds");
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("honest note-spend proves through the emitted descriptor");
        let blob = postcard::to_allocvec(&proof).expect("postcard-encode Ir2BatchProof");
        (pis, blob)
    }

    /// The consumer leg (`verify_note_spend_descriptor2`) ACCEPTS an honest proof
    /// and REJECTS every tampered claim / corrupted blob — through the REAL
    /// `verify_vm_descriptor2`. The felt arg order matches the retired
    /// `verify_note_spend_dsl_full`: (nullifier, root, value_lo, value_hi, asset,
    /// dest).
    #[test]
    fn honest_note_spend_verifies_and_tamper_rejects() {
        let w = make_witness(0x10);
        let (pis, blob) = prove_blob(&w);

        // pis layout (descriptor order): [nullifier, merkle_root, value_lo,
        // asset_type, destination_federation, value_hi, mint_hash].
        let (null, root, value_lo, asset, dest, value_hi) =
            (pis[0], pis[1], pis[2], pis[3], pis[4], pis[5]);

        // The executor leg re-derives the appended mint identity from the six
        // source felts; it must match the witness's 7th PI (guards our PI order).
        assert_eq!(
            note_spend_mint_hash_felt(null, root, value_lo, asset, dest, value_hi),
            pis[6],
            "reconstructed mint identity must equal the witness's appended 7th PI"
        );

        let verify = |nullifier, root, value_lo, value_hi, asset, dest, bytes: &[u8]| {
            super::verify_note_spend_descriptor2(
                nullifier, root, value_lo, value_hi, asset, dest, bytes,
            )
        };

        // HONEST ACCEPT — non-vacuity: the accept path is genuinely reached.
        assert!(
            verify(null, root, value_lo, value_hi, asset, dest, &blob).is_ok(),
            "honest note-spend proof must verify through the descriptor leg"
        );

        // REJECT — wrong nullifier claim (row-0 NULLIFIER boundary pin).
        assert!(
            verify(
                null + BabyBear::ONE,
                root,
                value_lo,
                value_hi,
                asset,
                dest,
                &blob
            )
            .is_err(),
            "a mismatched nullifier claim must be REJECTED"
        );
        // REJECT — wrong merkle root (last-row root pin + MINT_ROOT pin).
        assert!(
            verify(
                null,
                root + BabyBear::ONE,
                value_lo,
                value_hi,
                asset,
                dest,
                &blob
            )
            .is_err(),
            "a mismatched merkle root must be REJECTED (membership binding)"
        );
        // REJECT — wrong upper value limb (full-u64 binding, VALUE_HI pin).
        assert!(
            verify(
                null,
                root,
                value_lo,
                value_hi + BabyBear::ONE,
                asset,
                dest,
                &blob
            )
            .is_err(),
            "a mismatched value_hi (upper limb) must be REJECTED (no 30-bit collision)"
        );
        // REJECT — wrong asset type (ASSET_TYPE pin).
        assert!(
            verify(
                null,
                root,
                value_lo,
                value_hi,
                asset + BabyBear::ONE,
                dest,
                &blob
            )
            .is_err(),
            "a mismatched asset type must be REJECTED"
        );
        // REJECT — wrong destination federation (cross-federation replay tooth).
        assert!(
            verify(
                null,
                root,
                value_lo,
                value_hi,
                asset,
                dest + BabyBear::ONE,
                &blob
            )
            .is_err(),
            "a mismatched destination federation must be REJECTED (replay closed)"
        );
        // REJECT — a corrupted proof blob (postcard decode / verify failure).
        let mut corrupt = blob.clone();
        *corrupt.last_mut().unwrap() ^= 0xFF;
        assert!(
            verify(null, root, value_lo, value_hi, asset, dest, &corrupt).is_err(),
            "a corrupted proof blob must be REJECTED"
        );
        // REJECT — an empty blob (fail-closed decode; never a legacy fallback).
        assert!(
            verify(null, root, value_lo, value_hi, asset, dest, &[]).is_err(),
            "an empty proof blob must be REJECTED"
        );
    }

    /// A proof for witness A must NOT verify against witness B's claim tuple —
    /// the descriptor binds the WHOLE identity, not just a shape.
    #[test]
    fn proof_for_one_note_rejects_another_notes_claim() {
        let (_pis_a, blob_a) = prove_blob(&make_witness(0x20));
        let (pis_b, _blob_b) = prove_blob(&make_witness(0x21));

        let r = super::verify_note_spend_descriptor2(
            pis_b[0], pis_b[1], pis_b[2], pis_b[5], pis_b[3], pis_b[4], &blob_a,
        );
        assert!(
            r.is_err(),
            "note A's proof must be REJECTED against note B's claim tuple"
        );
    }
}
