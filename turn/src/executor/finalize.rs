//! Post-execution computation: cost metering, conservation checks, journal-to-delta conversion, receipt-side collectors.
//!
//! Extracted from `executor/mod.rs` (lines 9566-10532 of pre-decomposition file).

use super::*;

impl TurnExecutor {
    /// Compute the cost of a single effect.
    pub(super) fn compute_effect_cost(&self, effect: &Effect) -> u64 {
        let base = self.costs.effect_base;
        let extra = match effect {
            Effect::Transfer { .. } => self.costs.transfer,
            Effect::CreateCell { .. } => self.costs.create_cell,
            Effect::SetField { .. } => 0,
            Effect::GrantCapability { .. } => self.costs.effect_base,
            Effect::RevokeCapability { .. } => 0,
            Effect::EmitEvent { event, .. } => (event.data.len() as u64) * self.costs.per_byte * 32,
            Effect::IncrementNonce { .. } => 0,
            Effect::SetPermissions { .. } => self.costs.effect_base,
            Effect::SetVerificationKey { .. } => self.costs.effect_base,
            Effect::SetProgram { .. } => self.costs.effect_base,
            Effect::NoteSpend { .. } => self.costs.proof_verify, // note spends carry a proof
            Effect::NoteCreate { .. } => self.costs.effect_base,
            Effect::BridgeMint { .. } => self.costs.proof_verify, // bridge mints verify a STARK proof
            Effect::PipelinedSend { .. } => self.costs.effect_base,

            Effect::Introduce { .. } => self.costs.effect_base,
            Effect::SpawnWithDelegation { .. } => self.costs.create_cell,
            Effect::RefreshDelegation { .. } => self.costs.effect_base,
            Effect::RevokeDelegation { .. } => self.costs.effect_base,

            Effect::ExerciseViaCapability { inner_effects, .. } => {
                // Base cost + cost of each inner effect
                inner_effects
                    .iter()
                    .map(|e| self.compute_effect_cost(e))
                    .sum::<u64>()
            }

            Effect::MakeSovereign { .. } => self.costs.effect_base,
            Effect::CreateCellFromFactory { .. } => self.costs.create_cell,

            // CapTP runtime effects (P1.A): each is a simple state bump
            // (counter / use_count / refcount) plus a federation-mirror
            // hook on commit; cost is one effect_base.

            // Refusal: a non-action attestation. Cost is effect_base plus
            // proof-verify (the carried non-action witness goes through
            // the witnessed-predicate registry).
            Effect::Refusal { .. } => self
                .costs
                .effect_base
                .saturating_add(self.costs.proof_verify),
            // Lifecycle transitions: structural state mutations with no
            // proof verification; each is one effect_base.
            Effect::CellSeal { .. }
            | Effect::CellUnseal { .. }
            | Effect::CellDestroy { .. }
            | Effect::ReceiptArchive { .. } => self.costs.effect_base,
            // Burn: a balance mutation analogous to Transfer's effect_base
            // + transfer cost.
            Effect::Burn { .. } => self.costs.effect_base.saturating_add(self.costs.transfer),
            // Mint: the dual balance mutation (well→holder), same cost shape.
            Effect::Mint { .. } => self.costs.effect_base.saturating_add(self.costs.transfer),
            // AttenuateCapability: an in-place c-list mutation, like
            // GrantCapability.
            Effect::AttenuateCapability { .. } => self.costs.effect_base,
            // Promise / Notify deposit a promise-hole (a registry insert): one
            // effect_base. React discharges a hole by verifying a resolution
            // proof and spending the hole-id nullifier — proof_verify, like
            // NoteSpend.
            Effect::Promise { .. } | Effect::Notify { .. } => self.costs.effect_base,
            Effect::React { .. } => self.costs.proof_verify,
            // Shielded transfer: per-input hidden-STARK verify + Pedersen
            // conservation/range verify — proof-heavy, charged as a proof_verify.
            Effect::ShieldedTransfer { .. } => self.costs.proof_verify,
        };
        base.saturating_add(extra)
            .saturating_add((effect.data_bytes() as u64).saturating_mul(self.costs.per_byte))
    }

    /// Estimate the cost of a tree (without actually applying it).
    pub(super) fn estimate_tree_cost(&self, tree: &CallTree) -> u64 {
        let mut total = self.costs.action_base;

        total = total.saturating_add(match &tree.action.authorization {
            Authorization::Signature(_, _) => self.costs.signature_verify,
            Authorization::Proof { .. } => self.costs.proof_verify,
            Authorization::Breadstuff(_) => self.costs.signature_verify / 2,
            Authorization::Bearer(_) => self.costs.signature_verify,
            Authorization::Unchecked => 0,
            Authorization::CapTpDelivered { .. } => self.costs.signature_verify.saturating_mul(2),
            Authorization::HybridSignature { .. } => self.costs.signature_verify.saturating_mul(2),
            Authorization::Custom { .. } => self.costs.proof_verify,
            Authorization::OneOf { candidates, .. } => candidates
                .iter()
                .map(|c| estimate_authorization_cost(c, &self.costs))
                .max()
                .unwrap_or(0),
            Authorization::Stealth { .. } => self.costs.signature_verify,
            Authorization::Token { .. } => self.costs.proof_verify,
        });

        for effect in &tree.action.effects {
            total = total.saturating_add(self.compute_effect_cost(effect));
        }

        for child in &tree.children {
            total = total.saturating_add(self.estimate_tree_cost(child));
        }

        total
    }

    /// Compute a fresh state hash from the ledger by iterating all cells.
    #[allow(dead_code)]
    pub(super) fn compute_state_hash(ledger: &Ledger) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        let mut entries: Vec<_> = ledger.iter().collect();
        entries.sort_by_key(|(id, _)| *id.as_bytes());
        for (id, cell) in entries {
            hasher.update(id.as_bytes());
            hasher.update(cell.public_key());
            hasher.update(cell.token_id());
            hasher.update(&cell.state.nonce().to_le_bytes());
            // THE EPOCH §5: signed balance, the biased two-limb boundary
            // encoding (coherent with the v6 canonical commitment).
            hasher.update(&dregg_cell::state::encode_balance_le(cell.state.balance()));
            for field in &cell.state.fields {
                hasher.update(field);
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Check note conservation across all effects in the turn.
    ///
    /// Dispatches between two paths:
    /// - **Cleartext path**: all notes lack `value_commitment` -- uses sum comparison.
    /// - **Committed path**: all notes have `value_commitment` -- uses Pedersen/Schnorr
    ///   algebraic verification via the turn's `conservation_proof`.
    /// - **Mixed**: some notes have commitments and some don't -- rejected.
    ///
    /// Returns Ok(()) if conservation holds, or Err((asset_type, inputs, outputs)).
    pub(super) fn check_note_conservation(&self, turn: &Turn) -> Result<(), (u64, u64, u64)> {
        let mode = Self::detect_commitment_mode(&turn.call_forest);

        match mode {
            NoteCommitmentMode::Cleartext => {
                let mut inputs: std::collections::HashMap<u64, u64> =
                    std::collections::HashMap::new();
                let mut outputs: std::collections::HashMap<u64, u64> =
                    std::collections::HashMap::new();

                self.collect_note_effects(&turn.call_forest, &mut inputs, &mut outputs)?;

                let all_asset_types: std::collections::HashSet<u64> =
                    inputs.keys().chain(outputs.keys()).copied().collect();

                for asset_type in all_asset_types {
                    let input_total = inputs.get(&asset_type).copied().unwrap_or(0);
                    let output_total = outputs.get(&asset_type).copied().unwrap_or(0);
                    if input_total != output_total {
                        return Err((asset_type, input_total, output_total));
                    }
                }
                Ok(())
            }
            NoteCommitmentMode::Committed => {
                Self::check_committed_conservation(turn).map_err(|_| (0u64, 0u64, 0u64))
            }
            NoteCommitmentMode::Mixed => Err((0u64, 0u64, 0u64)),
            NoteCommitmentMode::Empty => Ok(()),
        }
    }

    /// Check conservation using the committed (Pedersen) path.
    pub(super) fn check_committed_conservation(turn: &Turn) -> Result<(), TurnError> {
        let proof_bytes = turn.conservation_proof.as_ref().ok_or_else(|| {
            TurnError::CommittedConservationFailed {
                reason: "turn uses committed values but has no conservation_proof".into(),
            }
        })?;

        let proof: dregg_cell_crypto::ConservationProof = postcard::from_bytes(proof_bytes)
            .map_err(|e| TurnError::CommittedConservationFailed {
                reason: format!("failed to deserialize conservation_proof: {e}"),
            })?;

        let mut input_commitments: Vec<ValueCommitment> = Vec::new();
        let mut output_commitments: Vec<ValueCommitment> = Vec::new();
        Self::collect_committed_notes(
            &turn.call_forest,
            &mut input_commitments,
            &mut output_commitments,
        )?;

        let turn_hash = turn.hash();
        dregg_cell_crypto::verify_conservation(
            &input_commitments,
            &output_commitments,
            &proof,
            &turn_hash,
        )
        .map_err(|e| TurnError::CommittedConservationFailed {
            reason: format!("conservation proof invalid: {e}"),
        })?;

        Self::verify_output_range_proofs(&turn.call_forest)?;
        Ok(())
    }

    /// Collect ValueCommitment points from committed NoteSpend/NoteCreate effects.
    pub(super) fn collect_committed_notes(
        forest: &crate::forest::CallForest,
        inputs: &mut Vec<ValueCommitment>,
        outputs: &mut Vec<ValueCommitment>,
    ) -> Result<(), TurnError> {
        for tree in &forest.roots {
            Self::collect_committed_notes_tree(tree, inputs, outputs)?;
        }
        Ok(())
    }

    pub(super) fn collect_committed_notes_tree(
        tree: &CallTree,
        inputs: &mut Vec<ValueCommitment>,
        outputs: &mut Vec<ValueCommitment>,
    ) -> Result<(), TurnError> {
        for effect in &tree.action.effects {
            Self::collect_committed_notes_from_effect(effect, inputs, outputs)?;
        }
        for child in &tree.children {
            Self::collect_committed_notes_tree(child, inputs, outputs)?;
        }
        Ok(())
    }

    pub(super) fn collect_committed_notes_from_effect(
        effect: &Effect,
        inputs: &mut Vec<ValueCommitment>,
        outputs: &mut Vec<ValueCommitment>,
    ) -> Result<(), TurnError> {
        match effect {
            Effect::NoteSpend {
                value_commitment: Some(vc_bytes),
                ..
            } => {
                let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes)).ok_or_else(
                    || TurnError::CommittedConservationFailed {
                        reason: "NoteSpend value_commitment is not a valid Ristretto point".into(),
                    },
                )?;
                inputs.push(vc);
            }
            Effect::NoteCreate {
                value_commitment: Some(vc_bytes),
                ..
            } => {
                let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes)).ok_or_else(
                    || TurnError::CommittedConservationFailed {
                        reason: "NoteCreate value_commitment is not a valid Ristretto point".into(),
                    },
                )?;
                outputs.push(vc);
            }
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    Self::collect_committed_notes_from_effect(inner, inputs, outputs)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Verify range proofs on NoteCreate outputs with value commitments.
    pub(super) fn verify_output_range_proofs(
        forest: &crate::forest::CallForest,
    ) -> Result<(), TurnError> {
        for tree in &forest.roots {
            Self::verify_output_range_proofs_tree(tree)?;
        }
        Ok(())
    }

    pub(super) fn verify_output_range_proofs_tree(tree: &CallTree) -> Result<(), TurnError> {
        for effect in &tree.action.effects {
            Self::verify_output_range_proof_effect(effect)?;
        }
        for child in &tree.children {
            Self::verify_output_range_proofs_tree(child)?;
        }
        Ok(())
    }

    pub(super) fn verify_output_range_proof_effect(effect: &Effect) -> Result<(), TurnError> {
        match effect {
            Effect::NoteCreate {
                value_commitment: Some(vc_bytes),
                range_proof,
                ..
            } => {
                let rp =
                    range_proof
                        .as_ref()
                        .ok_or_else(|| TurnError::CommittedConservationFailed {
                            reason: "NoteCreate has value_commitment but no range_proof".into(),
                        })?;
                if rp.is_empty() {
                    return Err(TurnError::CommittedConservationFailed {
                        reason: "NoteCreate range_proof is empty".into(),
                    });
                }
                // Deserialize the value commitment from the 32-byte compressed point.
                let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes)).ok_or_else(
                    || TurnError::CommittedConservationFailed {
                        reason: "NoteCreate value_commitment is not a valid Ristretto point".into(),
                    },
                )?;
                // Deserialize and verify the Bulletproof range proof.
                let bulletproof = BulletproofRangeProof {
                    proof_bytes: rp.clone(),
                };
                bulletproof.verify_range(&vc).map_err(|e| {
                    TurnError::CommittedConservationFailed {
                        reason: format!("NoteCreate range proof verification failed: {}", e),
                    }
                })?;
                Ok(())
            }
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    Self::verify_output_range_proof_effect(inner)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Detect whether the turn's notes use commitments, cleartext, or a mix.
    pub(super) fn detect_commitment_mode(forest: &crate::forest::CallForest) -> NoteCommitmentMode {
        let mut has_committed = false;
        let mut has_cleartext = false;

        for tree in &forest.roots {
            Self::detect_commitment_mode_tree(tree, &mut has_committed, &mut has_cleartext);
        }

        match (has_committed, has_cleartext) {
            (false, false) => NoteCommitmentMode::Empty,
            (true, false) => NoteCommitmentMode::Committed,
            (false, true) => NoteCommitmentMode::Cleartext,
            (true, true) => NoteCommitmentMode::Mixed,
        }
    }

    pub(super) fn detect_commitment_mode_tree(
        tree: &CallTree,
        has_committed: &mut bool,
        has_cleartext: &mut bool,
    ) {
        for effect in &tree.action.effects {
            Self::detect_commitment_mode_effect(effect, has_committed, has_cleartext);
        }
        for child in &tree.children {
            Self::detect_commitment_mode_tree(child, has_committed, has_cleartext);
        }
    }

    pub(super) fn detect_commitment_mode_effect(
        effect: &Effect,
        has_committed: &mut bool,
        has_cleartext: &mut bool,
    ) {
        match effect {
            Effect::NoteSpend {
                value_commitment, ..
            } => {
                if value_commitment.is_some() {
                    *has_committed = true;
                } else {
                    *has_cleartext = true;
                }
            }
            Effect::NoteCreate {
                value_commitment, ..
            } => {
                if value_commitment.is_some() {
                    *has_committed = true;
                } else {
                    *has_cleartext = true;
                }
            }
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    Self::detect_commitment_mode_effect(inner, has_committed, has_cleartext);
                }
            }
            _ => {}
        }
    }

    /// Recursively collect NoteSpend/NoteCreate effects from the call forest.
    pub(super) fn collect_note_effects(
        &self,
        forest: &crate::forest::CallForest,
        inputs: &mut std::collections::HashMap<u64, u64>,
        outputs: &mut std::collections::HashMap<u64, u64>,
    ) -> Result<(), (u64, u64, u64)> {
        for tree in &forest.roots {
            self.collect_note_effects_tree(tree, inputs, outputs)?;
        }
        Ok(())
    }

    /// Recursively collect note effects from a single tree.
    pub(super) fn collect_note_effects_tree(
        &self,
        tree: &CallTree,
        inputs: &mut std::collections::HashMap<u64, u64>,
        outputs: &mut std::collections::HashMap<u64, u64>,
    ) -> Result<(), (u64, u64, u64)> {
        for effect in &tree.action.effects {
            Self::collect_note_effects_from_effect(effect, inputs, outputs)?;
        }
        for child in &tree.children {
            self.collect_note_effects_tree(child, inputs, outputs)?;
        }
        Ok(())
    }

    /// Collect note effects from a single effect, recursing into ExerciseViaCapability.
    pub(super) fn collect_note_effects_from_effect(
        effect: &Effect,
        inputs: &mut std::collections::HashMap<u64, u64>,
        outputs: &mut std::collections::HashMap<u64, u64>,
    ) -> Result<(), (u64, u64, u64)> {
        match effect {
            Effect::NoteSpend {
                value, asset_type, ..
            } => {
                let entry = inputs.entry(*asset_type).or_insert(0);
                *entry = entry
                    .checked_add(*value)
                    .ok_or((*asset_type, u64::MAX, 0))?;
            }
            Effect::NoteCreate {
                value, asset_type, ..
            } => {
                let entry = outputs.entry(*asset_type).or_insert(0);
                *entry = entry
                    .checked_add(*value)
                    .ok_or((*asset_type, 0, u64::MAX))?;
            }
            Effect::BridgeMint { portable_proof } => {
                // BridgeMint contributes to BOTH sides of conservation:
                // it's an external input (from another federation) AND creates output.
                // For local conservation, bridge mints are treated as matching
                // input+output (self-balancing) since the value comes from outside.
                let entry = inputs.entry(portable_proof.asset_type).or_insert(0);
                *entry = entry.checked_add(portable_proof.value).ok_or((
                    portable_proof.asset_type,
                    u64::MAX,
                    0,
                ))?;
                let entry = outputs.entry(portable_proof.asset_type).or_insert(0);
                *entry = entry.checked_add(portable_proof.value).ok_or((
                    portable_proof.asset_type,
                    0,
                    u64::MAX,
                ))?;
            }
            // Recurse into ExerciseViaCapability inner effects to catch nested
            // NoteSpend/NoteCreate that would otherwise bypass the conservation check.
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    Self::collect_note_effects_from_effect(inner, inputs, outputs)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Compute the BLAKE3 hash of all effect hashes combined.
    pub(super) fn compute_effects_hash(&self, effect_hashes: &[[u8; 32]]) -> [u8; 32] {
        if effect_hashes.is_empty() {
            return [0u8; 32];
        }
        let mut hasher = blake3::Hasher::new();
        for h in effect_hashes {
            hasher.update(h);
        }
        *hasher.finalize().as_bytes()
    }

    /// Compute a LedgerDelta from journal entries and the current (post-mutation) ledger.
    ///
    /// The journal records the old (pre-mutation) values. By comparing those to the
    /// current state in the ledger, we derive the delta without needing a full ledger snapshot.
    pub(super) fn compute_delta_from_journal(
        journal: &LedgerJournal,
        ledger: &Ledger,
    ) -> LedgerDelta {
        use std::collections::{HashMap, HashSet};

        let mut delta = LedgerDelta::new();
        let mut created_cells: HashSet<CellId> = HashSet::new();
        let mut updated_cells: HashMap<CellId, CellStateDelta> = HashMap::new();

        // Track the FIRST old balance/nonce per cell (the pre-turn value).
        let mut first_balance: HashMap<CellId, i64> = HashMap::new();
        let mut first_nonce: HashMap<CellId, u64> = HashMap::new();
        let mut first_fields: HashMap<(CellId, usize), Option<FieldElement>> = HashMap::new();

        for entry in journal.entries() {
            match entry {
                JournalEntry::CreateCell { cell } => {
                    if let Some(c) = ledger.get(cell) {
                        delta.created.push(c.clone());
                        created_cells.insert(*cell);
                    }
                }
                JournalEntry::SetField {
                    cell,
                    index,
                    old_value,
                } => {
                    if !created_cells.contains(cell) {
                        first_fields.entry((*cell, *index)).or_insert(*old_value);
                    }
                }
                JournalEntry::SetBalance { cell, old_balance } => {
                    if !created_cells.contains(cell) {
                        first_balance.entry(*cell).or_insert(*old_balance);
                    }
                }
                JournalEntry::SetNonce { cell, old_nonce } => {
                    if !created_cells.contains(cell) {
                        first_nonce.entry(*cell).or_insert(*old_nonce);
                    }
                }
                JournalEntry::GrantCapability { cell, slot } => {
                    if !created_cells.contains(cell) {
                        if let Some(c) = ledger.get(cell) {
                            if let Some(cap_ref) = c.capabilities.lookup(*slot) {
                                let e = updated_cells
                                    .entry(*cell)
                                    .or_insert_with(CellStateDelta::empty);
                                e.capability_grants.push(cap_ref.clone());
                            }
                        }
                    }
                }
                JournalEntry::RevokeCapability { cell, old_cap } => {
                    if !created_cells.contains(cell) {
                        let e = updated_cells
                            .entry(*cell)
                            .or_insert_with(CellStateDelta::empty);
                        e.capability_revocations.push(old_cap.slot);
                    }
                }
                JournalEntry::SetProvedState { .. } => {
                    // proved_state changes are tracked implicitly through the cell's state;
                    // no separate delta field needed for now.
                }
                JournalEntry::SetPermissions { cell, .. } => {
                    if !created_cells.contains(cell) {
                        let e = updated_cells
                            .entry(*cell)
                            .or_insert_with(CellStateDelta::empty);
                        // Record that permissions changed (the new perms are on the cell now).
                        if let Some(c) = ledger.get(cell) {
                            e.permission_changes = Some(c.permissions.clone());
                        }
                    }
                }
                JournalEntry::SetVerificationKey { .. } => {
                    // Verification key changes don't have a delta field currently;
                    // tracked via the cell's state.
                }
                JournalEntry::SetProgram { .. } => {
                    // Program (caveat table) changes don't have a delta field
                    // currently; tracked via the cell's state. (The in-circuit
                    // witness — a descriptor rung binding the program write — is
                    // the VK-affecting follow-up.)
                }
                JournalEntry::SetDelegation { .. }
                | JournalEntry::SetDelegationEpoch { .. }
                | JournalEntry::SetCommittedHeight { .. } => {}
                // Note/obligation/event/escrow entries don't affect the ledger delta directly.
                // Obligation/escrow/nullifier insertion entries are rollback-only bookkeeping.
                JournalEntry::NoteSpend
                | JournalEntry::NoteCreate
                | JournalEntry::EventEmitted { .. }
                | JournalEntry::BridgedNullifierInserted { .. }
                | JournalEntry::NoteNullifierInserted { .. }
                | JournalEntry::NoteCommitmentInserted { .. }
                // A revocation insert into `note_revoked` is rollback-only
                // bookkeeping (undone by `LedgerJournal::rollback`); it commits
                // via the rotated `revoked_root` group, not the LedgerDelta —
                // the revocation-side sibling of the nullifier/commitment inserts.
                | JournalEntry::RevocationInserted { .. } => {}
                // Lifecycle / capability narrowing: rollback-only — no
                // separate LedgerDelta field today. On commit the cell's
                // CellLifecycle / CapabilityRef change is read off the
                // cell itself; verifiers re-execute against the canonical
                // commitment which folds the lifecycle byte in (see
                // cell/src/commitment.rs).
                JournalEntry::SetLifecycle { .. } | JournalEntry::AttenuateCapability { .. } => {}
                // Heap writes: rollback-only here — no separate LedgerDelta
                // field. On commit the cell's updated `heap_root` (and its
                // `heap_map` preimage) is read off the cell itself; the
                // canonical commitment folds `heap_root` in (cell/src/state.rs).
                JournalEntry::SetHeap { .. } => {}
            }
        }

        // Compute field/balance/nonce deltas from first-old vs current.
        for ((cell_id, index), old_value) in &first_fields {
            if let Some(c) = ledger.get(cell_id) {
                let new_value = if *index < STATE_SLOTS {
                    Some(c.state.fields[*index])
                } else {
                    c.state.get_field_ext(*index as u64)
                };
                if new_value != *old_value {
                    let e = updated_cells
                        .entry(*cell_id)
                        .or_insert_with(CellStateDelta::empty);
                    e.field_updates
                        .push((*index, new_value.unwrap_or(FIELD_ZERO)));
                }
            }
        }

        for (cell_id, old_balance) in &first_balance {
            if let Some(c) = ledger.get(cell_id) {
                let diff = c.state.balance() as i128 - *old_balance as i128;
                if diff != 0 {
                    let e = updated_cells
                        .entry(*cell_id)
                        .or_insert_with(CellStateDelta::empty);
                    e.balance_change =
                        i64::try_from(diff).unwrap_or(if diff > 0 { i64::MAX } else { i64::MIN });
                }
            }
        }

        for (cell_id, old_nonce) in &first_nonce {
            if let Some(c) = ledger.get(cell_id) {
                if c.state.nonce() > *old_nonce {
                    let e = updated_cells
                        .entry(*cell_id)
                        .or_insert_with(CellStateDelta::empty);
                    e.nonce_increment = true;
                }
            }
        }

        // Collect non-empty cell deltas.
        for (cell_id, cell_delta) in updated_cells {
            if !cell_delta.field_updates.is_empty()
                || cell_delta.nonce_increment
                || cell_delta.balance_change != 0
                || cell_delta.permission_changes.is_some()
                || !cell_delta.capability_grants.is_empty()
                || !cell_delta.capability_revocations.is_empty()
            {
                delta.updated.push((cell_id, cell_delta));
            }
        }

        delta
    }

    /// Compute a LedgerDelta including the Phase 1 fee + nonce commitment and
    /// Phase 3 fee distribution (proposer/treasury/fee-well credits).
    ///
    /// Since Phase 1 (fee/nonce) and Phase 3 (distribution) are committed outside
    /// the journal, we need to account for them separately in the delta. The agent's
    /// balance decreased by `fee` and nonce incremented by 1. The proposer receives
    /// 50% and treasury receives 30% (if configured and present in ledger); the
    /// remainder MOVES to the fee well (THE EPOCH §5, "fees as moves"), so the
    /// delta sums to exactly zero when a fee well is configured.
    pub(super) fn compute_delta_from_journal_with_fee(
        journal: &LedgerJournal,
        ledger: &Ledger,
        agent: &CellId,
        fee: u64,
        proposer_cell: Option<&CellId>,
        treasury_cell: Option<&CellId>,
        fee_well_cell: Option<&CellId>,
    ) -> LedgerDelta {
        let mut delta = Self::compute_delta_from_journal(journal, ledger);

        // Check if the agent already appears in updated cells.
        let agent_already_updated = delta.updated.iter().any(|(id, _)| id == agent);

        if agent_already_updated {
            // Adjust the existing delta for the agent to include the fee.
            for (id, cell_delta) in &mut delta.updated {
                if id == agent {
                    cell_delta.balance_change -= fee as i64;
                    cell_delta.nonce_increment = true;
                    break;
                }
            }
        } else {
            // Agent only had Phase 1 changes (fee + nonce), add a new delta entry.
            let mut cell_delta = CellStateDelta::empty();
            cell_delta.balance_change = -(fee as i64);
            cell_delta.nonce_increment = true;
            delta.updated.push((*agent, cell_delta));
        }

        // Account for fee distribution credits (Phase 3). Track what was
        // actually delivered so the fee-well move below closes the books
        // exactly (mirrors `distribute_fee_shares`).
        let proposer_share = fee / 2;
        let treasury_share = fee * 3 / 10;
        let mut delivered: u64 = 0;

        if let Some(proposer_id) = proposer_cell {
            // Only include in delta if proposer exists in ledger.
            if ledger.get(proposer_id).is_some() {
                let proposer_in_delta = delta.updated.iter_mut().find(|(id, _)| id == proposer_id);
                if let Some((_, cell_delta)) = proposer_in_delta {
                    cell_delta.balance_change += proposer_share as i64;
                } else {
                    let mut cell_delta = CellStateDelta::empty();
                    cell_delta.balance_change = proposer_share as i64;
                    delta.updated.push((*proposer_id, cell_delta));
                }
                delivered += proposer_share;
            }
        }

        if let Some(treasury_id) = treasury_cell {
            // Only include in delta if treasury exists in ledger.
            if ledger.get(treasury_id).is_some() {
                let treasury_in_delta = delta.updated.iter_mut().find(|(id, _)| id == treasury_id);
                if let Some((_, cell_delta)) = treasury_in_delta {
                    cell_delta.balance_change += treasury_share as i64;
                } else {
                    let mut cell_delta = CellStateDelta::empty();
                    cell_delta.balance_change = treasury_share as i64;
                    delta.updated.push((*treasury_id, cell_delta));
                }
                delivered += treasury_share;
            }
        }

        // THE EPOCH §5: the undelivered remainder moves to the fee well.
        if let Some(well_id) = fee_well_cell {
            if ledger.get(well_id).is_some() && fee > delivered {
                let well_in_delta = delta.updated.iter_mut().find(|(id, _)| id == well_id);
                if let Some((_, cell_delta)) = well_in_delta {
                    cell_delta.balance_change += (fee - delivered) as i64;
                } else {
                    let mut cell_delta = CellStateDelta::empty();
                    cell_delta.balance_change = (fee - delivered) as i64;
                    delta.updated.push((*well_id, cell_delta));
                }
            }
        }

        delta
    }

    /// Derive a synthetic CellId for a seal pair's sealer or unsealer capability.
    // Canonical seal-capability-id derivation; kept as the authoritative reference
    // the coverage tests (`cap_hygiene_r7_b2`, `coverage_misc_effects`) replicate and
    // check against, even though no in-crate call site currently invokes it.
    #[allow(dead_code)]
    pub(super) fn seal_capability_id(pair_id: &[u8; 32], is_sealer: bool) -> CellId {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-seal capability-id v1");
        hasher.update(pair_id);
        hasher.update(if is_sealer { b"sealer" } else { b"unsealer" });
        CellId::from_bytes(*hasher.finalize().as_bytes())
    }

    /// Collect emitted events from the journal for inclusion in the turn receipt.
    /// Recursive: does any action in the forest carry an `Effect::Burn`?
    /// Drives the `was_burn` flag in the receipt so the non-conservation
    /// disclosure is committed (Silver-Vision lifecycle plan).
    pub(super) fn forest_carries_burn(forest: &crate::forest::CallForest) -> bool {
        forest.roots.iter().any(tree_has_burn_effect)
    }

    pub(super) fn collect_emitted_events(journal: &LedgerJournal) -> Vec<EmittedEvent> {
        journal
            .entries()
            .iter()
            .filter_map(|entry| match entry {
                JournalEntry::EventEmitted { cell, topic, data } => Some(EmittedEvent {
                    cell: *cell,
                    topic: *topic,
                    data: data.clone(),
                }),
                _ => None,
            })
            .collect()
    }

    pub(super) fn collect_routing_directives(
        forest: &crate::forest::CallForest,
        turn_hash: &[u8; 32],
        block_height: u64,
        max_introduction_lifetime: u64,
    ) -> Vec<RoutingDirective> {
        let mut directives = Vec::new();
        for tree in &forest.roots {
            Self::collect_routing_directives_tree(
                tree,
                turn_hash,
                block_height,
                max_introduction_lifetime,
                &mut directives,
            );
        }
        directives
    }

    pub(super) fn collect_routing_directives_tree(
        tree: &CallTree,
        turn_hash: &[u8; 32],
        block_height: u64,
        max_introduction_lifetime: u64,
        directives: &mut Vec<RoutingDirective>,
    ) {
        for effect in &tree.action.effects {
            if let Effect::Introduce {
                recipient, target, ..
            } = effect
            {
                directives.push(RoutingDirective {
                    sender: *recipient,
                    target: *target,
                    authorizing_turn: *turn_hash,
                    expires: Some(block_height + max_introduction_lifetime),
                });
            }
        }
        for child in &tree.children {
            Self::collect_routing_directives_tree(
                child,
                turn_hash,
                block_height,
                max_introduction_lifetime,
                directives,
            );
        }
    }

    /// Collect GC export registrations from introductions in the call forest.
    ///
    /// For each `Effect::Introduce { target, recipient, .. }`, emits an
    /// `IntroductionExport` record. The node/server layer uses these to call
    /// `ExportGcManager::record_export(target, recipient_federation, height)`,
    /// ensuring that introduced capabilities participate in distributed GC.
    ///
    /// Without this, capabilities created via 3-party introductions bypass GC
    /// tracking entirely — no `DropRef` is ever fired, causing the export table
    /// to grow unboundedly.
    pub(super) fn collect_introduction_exports(
        forest: &crate::forest::CallForest,
        turn_hash: &[u8; 32],
        block_height: u64,
        max_introduction_lifetime: u64,
    ) -> Vec<crate::routing::IntroductionExport> {
        let mut exports = Vec::new();
        for tree in &forest.roots {
            Self::collect_introduction_exports_tree(
                tree,
                turn_hash,
                block_height,
                max_introduction_lifetime,
                &mut exports,
            );
        }
        exports
    }

    pub(super) fn collect_introduction_exports_tree(
        tree: &CallTree,
        turn_hash: &[u8; 32],
        block_height: u64,
        max_introduction_lifetime: u64,
        exports: &mut Vec<crate::routing::IntroductionExport>,
    ) {
        for effect in &tree.action.effects {
            if let Effect::Introduce {
                recipient, target, ..
            } = effect
            {
                exports.push(crate::routing::IntroductionExport {
                    target: *target,
                    recipient: *recipient,
                    authorizing_turn: *turn_hash,
                    expires: Some(block_height + max_introduction_lifetime),
                });
            }
        }
        for child in &tree.children {
            Self::collect_introduction_exports_tree(
                child,
                turn_hash,
                block_height,
                max_introduction_lifetime,
                exports,
            );
        }
    }

    /// Drain the CONSUMED-capability witnesses captured at the authorization
    /// sites during THIS turn (cap Phase C). The CONSUMED sibling of
    /// [`Self::collect_derivation_records`], which records capabilities the
    /// turn *creates* (Grant/Introduce/Spawn/Unseal); this drains the
    /// witnesses for the capabilities the turn *consumed* to be authorized
    /// (breadstuff / bearer-delegation — see
    /// `authorize.rs::record_consumed_cap_witness`). Self-sovereign turns
    /// (owner-signature authority) consume no capability and yield an empty
    /// vec.
    pub(super) fn take_consumed_cap_witnesses(&self) -> Vec<crate::turn::ConsumedCapWitness> {
        std::mem::take(
            &mut *self
                .consumed_cap_witnesses
                .lock()
                .unwrap_or_else(|e| e.into_inner()),
        )
    }

    /// Collect all capability derivation records from the call forest.
    ///
    /// Scans the forest for effects that create derivation edges:
    /// - GrantCapability: source grants to target
    /// - Introduce: introducer grants target access to recipient
    /// - SpawnWithDelegation: parent's c-list snapshot to child
    /// - Unseal: sealed capability recovered to recipient
    pub(super) fn collect_derivation_records(
        forest: &crate::forest::CallForest,
        timestamp: u64,
    ) -> Vec<dregg_cell::DerivationRecord> {
        let mut records = Vec::new();
        let mut slot_counter: u32 = 0;
        for tree in &forest.roots {
            Self::collect_derivation_records_tree(tree, timestamp, &mut records, &mut slot_counter);
        }
        records
    }

    pub(super) fn collect_derivation_records_tree(
        tree: &CallTree,
        timestamp: u64,
        records: &mut Vec<dregg_cell::DerivationRecord>,
        slot_counter: &mut u32,
    ) {
        for effect in &tree.action.effects {
            match effect {
                Effect::GrantCapability { from, to, cap } => {
                    records.push(dregg_cell::DerivationRecord {
                        target_cell: *to,
                        target_slot: *slot_counter,
                        edge: dregg_cell::DerivationEdge {
                            source_cell: *from,
                            source_slot: cap.slot,
                            derivation_type: dregg_cell::DerivationType::Grant,
                            // The source (parent) cap carries its own provenance in
                            // the effect; chaining it is what lets the ancestor-chain
                            // non-revocation gate catch this grant's descendants.
                            parent_provenance: cap.provenance,
                        },
                        created_at: timestamp,
                    });
                    *slot_counter += 1;
                }
                Effect::Introduce {
                    introducer,
                    recipient,
                    ..
                } => {
                    records.push(dregg_cell::DerivationRecord {
                        target_cell: *recipient,
                        target_slot: *slot_counter,
                        edge: dregg_cell::DerivationEdge {
                            source_cell: *introducer,
                            source_slot: 0,
                            derivation_type: dregg_cell::DerivationType::Introduce,
                            // PROVISIONAL root marker: the introducer's held cap over
                            // `target` is the real parent, but this effect carries no
                            // source-cap provenance and `source_slot` is already the
                            // 0 placeholder. Threading the real parent provenance
                            // needs ledger access in `collect_derivation_records_tree`
                            // — a design change (see lane report), not a guessed
                            // sentinel.
                            parent_provenance: dregg_cell::derivation::mint_provenance(),
                        },
                        created_at: timestamp,
                    });
                    *slot_counter += 1;
                }
                Effect::SpawnWithDelegation {
                    child_public_key,
                    child_token_id,
                    ..
                } => {
                    let child_id = CellId::derive_raw(child_public_key, child_token_id);
                    records.push(dregg_cell::DerivationRecord {
                        target_cell: child_id,
                        target_slot: *slot_counter,
                        edge: dregg_cell::DerivationEdge {
                            source_cell: tree.action.target,
                            source_slot: 0,
                            derivation_type: dregg_cell::DerivationType::Delegate,
                            // PROVISIONAL root marker: a spawn snapshots the parent's
                            // whole c-list, so no single parent cap provenance exists
                            // in this coarse one-record-per-spawn edge (source_slot is
                            // already the 0 placeholder). Threading real per-cap
                            // provenance needs ledger access — a design change (see
                            // lane report), not a guessed sentinel.
                            parent_provenance: dregg_cell::derivation::mint_provenance(),
                        },
                        created_at: timestamp,
                    });
                    *slot_counter += 1;
                }

                _ => {}
            }
        }
        for child in &tree.children {
            Self::collect_derivation_records_tree(child, timestamp, records, slot_counter);
        }
    }

    /// Re-stamp a (Rust-reference) committed receipt's `post_state_hash` to the AUTHORITATIVE
    /// installed (Lean) root and re-sign it, for the Stage-0 authority-inversion commit branch when
    /// the Rust reference ALSO committed. On the covered set the roots agree (the differential
    /// teeth), so this is a no-op re-stamp + re-sign; the override only ever fires on a surfaced Rust
    /// root-bug, where the receipt MUST attest the state actually committed (the Lean root), not the
    /// Rust reference's. Re-signs so `executor_signature` still binds the (possibly re-stamped) hash.
    pub fn restamp_committed_receipt(
        &self,
        mut receipt: TurnReceipt,
        authoritative_post_root: [u8; 32],
    ) -> TurnReceipt {
        receipt.post_state_hash = authoritative_post_root;
        receipt.executor_signature = None;
        receipt.executor_signature = self.maybe_sign_receipt(&receipt);
        receipt
    }

    /// Build the AUTHORITATIVE `Committed` `TurnResult` for the Stage-0 authority-inversion path
    /// when the VERIFIED Lean executor COMMITTED a turn the demoted Rust reference REJECTED (a Rust
    /// false-reject bug). The Lean post-state is already installed; this synthesizes the receipt that
    /// attests it, since there is no Rust receipt to carry.
    ///
    /// The receipt is built the same self-contained way as the proof-carrying early-commit path
    /// (`execute.rs`): `effects_hash`/`action_count` from the turn's call forest, a metering-proxy
    /// `computrons_used`, `pre_state_hash`/`post_state_hash` pinned to the pre/authoritative roots,
    /// signed if a key is configured, and a fee-aware (conservation-closed) ledger delta. It does NOT
    /// re-run the effect loop — the verified executor already adjudicated the transition; this is the
    /// honest attestation of its authoritative verdict.
    ///
    /// `pre_root` is the pre-state root (for `pre_state_hash`); `post_root` is the installed Lean
    /// post-state root.
    pub fn build_producer_committed_result(
        &self,
        turn: &Turn,
        pre_root: [u8; 32],
        post_root: [u8; 32],
    ) -> TurnResult {
        let pre_state_hash = pre_root;
        let turn_hash = turn.hash();
        let forest_hash = turn.call_forest.compute_hash();

        // effects_hash / action_count from the turn body (mirrors the proof-carrying commit path:
        // the canonical BLAKE3 fold over per-effect hashes the proof verifier keys to).
        let mut effect_hashes: Vec<[u8; 32]> = Vec::new();
        fn collect_effect_hashes(tree: &crate::forest::CallTree, out: &mut Vec<[u8; 32]>) {
            for effect in &tree.action.effects {
                out.push(crate::action::Effect::hash(effect));
            }
            for child in &tree.children {
                collect_effect_hashes(child, out);
            }
        }
        for root in &turn.call_forest.roots {
            collect_effect_hashes(root, &mut effect_hashes);
        }
        let effects_hash = self.compute_effects_hash(&effect_hashes);
        let action_count = turn.call_forest.action_count();
        let computrons_used = self.costs.effect_base.saturating_mul(action_count as u64);

        let mut receipt = TurnReceipt {
            turn_hash,
            forest_hash,
            pre_state_hash,
            post_state_hash: post_root,
            timestamp: self.current_timestamp,
            effects_hash,
            computrons_used,
            action_count,
            previous_receipt_hash: turn.previous_receipt_hash,
            agent: turn.agent,
            federation_id: self.local_federation_id,
            routing_directives: vec![],
            introduction_exports: vec![],
            derivation_records: vec![],
            emitted_events: vec![],
            executor_signature: None,
            finality: crate::turn::Finality::Final,
            was_encrypted: false,
            was_burn: Self::forest_carries_burn(&turn.call_forest),
            consumed_capabilities: self.take_consumed_cap_witnesses(),
        };
        receipt.executor_signature = self.maybe_sign_receipt(&receipt);

        // Fee-aware, conservation-closed delta (mirrors the proof-carrying path): the agent's fee
        // debit + nonce bump, with the fee distributed to proposer/treasury/fee-well so the delta
        // sums to zero.
        let mut delta = LedgerDelta::new();
        let mut agent_delta = dregg_cell::CellStateDelta::empty();
        agent_delta.balance_change = -(turn.fee as i64);
        agent_delta.nonce_increment = true;
        delta.updated.push((turn.agent, agent_delta));

        let mut fee_delivered: u64 = 0;
        if let Some(proposer_id) = &self.proposer_cell {
            let mut d = dregg_cell::CellStateDelta::empty();
            d.balance_change = (turn.fee / 2) as i64;
            fee_delivered += turn.fee / 2;
            delta.updated.push((*proposer_id, d));
        }
        if let Some(treasury_id) = &self.treasury_cell {
            let mut d = dregg_cell::CellStateDelta::empty();
            d.balance_change = (turn.fee * 3 / 10) as i64;
            fee_delivered += turn.fee * 3 / 10;
            delta.updated.push((*treasury_id, d));
        }
        if let Some(well_id) = &self.fee_well_cell {
            let mut d = dregg_cell::CellStateDelta::empty();
            d.balance_change = (turn.fee - fee_delivered) as i64;
            delta.updated.push((*well_id, d));
        }

        self.record_receipt_hash(turn.agent, receipt.receipt_hash());

        TurnResult::Committed {
            ledger_delta: delta,
            receipt,
            computrons_used,
        }
    }
}
