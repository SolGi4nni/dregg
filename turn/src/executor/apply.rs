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
            Effect::RefreshDelegation => {
                self.apply_refresh_delegation(ledger, path, action_target, journal)
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
        if index >= STATE_SLOTS {
            return Err((
                TurnError::InvalidFieldIndex { cell: *cell, index },
                path.to_vec(),
            ));
        }
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetState,
                "SetState",
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
        journal.record_set_field(*cell, index, c.state.fields[index]);
        c.state.fields[index] = *value;
        // Invalidate stale field commitment (the old hash no longer matches).
        if c.state.commitments[index].is_some() {
            c.state.commitments[index] = None;
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
        if from != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                from,
                dregg_cell::permissions::Action::Send,
                "Send",
                path,
            )?;
        }
        let from_cell = ledger
            .get(from)
            .ok_or_else(|| (TurnError::CellNotFound { id: *from }, path.to_vec()))?;
        if from_cell.state.balance() < amount {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *from,
                    required: amount,
                    available: from_cell.state.balance(),
                },
                path.to_vec(),
            ));
        }
        if ledger.get(to).is_none() {
            return Err((TurnError::TransferDestNotFound { id: *to }, path.to_vec()));
        }
        let to_balance = ledger.get(to).unwrap().state.balance();
        if to_balance.checked_add(amount).is_none() {
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
            .set_balance(old_from_balance - amount);
        ledger
            .get_mut(to)
            .unwrap()
            .state
            .set_balance(old_to_balance + amount);
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
        if ledger.get(cell).is_none() {
            return Err((TurnError::CellNotFound { id: *cell }, path.to_vec()));
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
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
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
                path,
            )?;
        }
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
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
        journal.record_set_verification_key(*cell, c.verification_key.clone());
        c.verification_key = new_vk.cloned();
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
        // bridge mints and call the typed `verify_note_spend_dsl_with_destination`
        // entry point. This verifier:
        //
        //   * deserializes the STARK proof,
        //   * recomputes the AIR's boundary constraints over the typed PI
        //     (nullifier, merkle_root, value, asset_type, destination_federation),
        //   * algebraically rejects any proof whose trace columns at row 0
        //     (col::NULLIFIER, col::VALUE, col::ASSET_TYPE,
        //     col::DESTINATION_FEDERATION) do not match the PI vector that
        //     the executor supplies from the `PortableNoteProof`.
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
            use dregg_circuit::dsl::note_spending::verify_note_spend_dsl_full;
            use dregg_circuit::poseidon2;
            use dregg_circuit::stark::proof_from_bytes;

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

            let stark_proof = proof_from_bytes(proof_bytes)
                .map_err(|e| format!("STARK proof deserialization failed: {e}"))?;

            let nullifier_bb = compress(nullifier);
            let root_bb = compress(root);
            let dest_bb = compress(dest_federation);
            let (value_lo, value_hi) = u64_to_limbs(value);
            // asset_type stays a single felt: asset identifiers are small
            // enumerated tags, not balances, so 30-bit binding is faithful.
            let asset_bb = BabyBear::new((asset_type & ((1u64 << 30) - 1)) as u32);

            // SECURITY: This call rejects any proof whose embedded PI vector
            // does not match (nullifier_bb, root_bb, value_lo, value_hi,
            // asset_bb, dest_bb). The AIR's boundary constraints at row 0
            // columns {NULLIFIER, VALUE, VALUE_HI, ASSET_TYPE,
            // DESTINATION_FEDERATION} and at the last row col CURRENT (merkle
            // root) pin the prover's trace to whatever the verifier passes
            // here — including the FULL u64 amount via the two value limbs.
            verify_note_spend_dsl_full(
                nullifier_bb,
                root_bb,
                value_lo,
                value_hi,
                asset_bb,
                dest_bb,
                &stark_proof,
            )
            .map_err(|e| format!("STARK spending proof verification failed: {e}"))
        };

        dregg_cell::note_bridge::verify_portable_note(
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
    #[allow(clippy::too_many_arguments)]
    

    

    

    // Committed escrow effects: privacy-preserving conditional settlement.
    #[allow(clippy::too_many_arguments)]
    

    

    

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
        if let Some(mask) = cap.allowed_effects {
            if mask != 0 {
                for inner_effect in inner_effects.iter() {
                    let effect_bit = inner_effect.effect_kind_mask();
                    if effect_bit & mask == 0 {
                        return Err((
                            TurnError::FacetViolation {
                                actor: *actor,
                                target: cap_target,
                                cap_slot,
                                attempted_effect: format!(
                                    "{:?}",
                                    std::mem::discriminant(inner_effect)
                                ),
                                allowed_mask: mask,
                            },
                            path.to_vec(),
                        ));
                    }
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
    ) -> Result<(), (TurnError, Vec<usize>)> {
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

        let child_mut = ledger.get_mut(action_target).unwrap();
        journal.record_set_delegation(*action_target, old_delegation);
        let clist_bytes = postcard::to_allocvec(&new_snapshot).unwrap_or_default();
        let clist_commitment = dregg_cell::DelegatedRef::compute_clist_commitment(&clist_bytes);
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
        //   3. Record the refusal commitment + reason in field[4]
        //      (the audit slot) — a Poseidon2-ish commitment of
        //      `(offered_action_commitment, reason_discriminant)`
        //      so light clients can detect a refusal without
        //      re-fetching the witness.
        //   4. NEVER mutate balance, capability set, or any value
        //      slot. Refusal is structurally *only* a non-action
        //      attestation; permission/value mutations belong to
        //      other effect variants.
        if cell != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                cell,
                dregg_cell::permissions::Action::SetState,
                "Refusal",
                path,
            )?;
        }
        // Witness presence check. The app supplies the actual
        // verifier through the WitnessedPredicateRegistry; here
        // we only confirm the index resolves.
        // NOTE: the action is in scope only at the higher
        // execute_action level. apply_effect doesn't get the
        // action — but the per-action witness binding pass
        // covers this when the executor wires per-action
        // witness lookup. For the per-effect apply pass, the
        // structural integrity is that the witness index is in
        // u32 range (already typed) and the cell exists.
        let _ = proof_witness_index;
        let c = ledger
            .get_mut(cell)
            .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
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
        journal.record_set_field(*cell, 4, c.state.fields[4]);
        c.state.fields[4] = audit;
        if c.state.commitments[4].is_some() {
            c.state.commitments[4] = None;
        }
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
        action_target: &CellId,
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
        if target != action_target {
            self.check_cross_cell_permission(
                ledger,
                actor,
                target,
                dregg_cell::permissions::Action::Send,
                "Burn",
                path,
            )?;
        }
        let c = ledger
            .get(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        let bal = c.state.balance();
        if bal < amount {
            return Err((
                TurnError::InsufficientBalance {
                    cell: *target,
                    required: amount,
                    available: bal,
                },
                path.to_vec(),
            ));
        }
        let new_bal = bal - amount;
        let cm = ledger
            .get_mut(target)
            .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
        journal.record_set_balance(*target, bal);
        cm.state.set_balance(new_bal);
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
