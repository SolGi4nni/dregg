//! Proof verification: STARK + bilateral + effect binding proofs, plus field/commitment conversion helpers for sovereign cells.
//!
//! Extracted from `executor/mod.rs` (lines 1279-2993 of pre-decomposition file).

use super::*;

impl TurnExecutor {
    /// TRUST-CRITICAL: This function bridges the TRUSTLESS layer (STARK proofs) into the
    /// executor. If compromised: forged sovereign state could be committed without valid proofs.
    /// However, this function is ALREADY close to trustless — it only verifies a proof and
    /// updates a commitment. The proof itself is independently verifiable.
    /// Future: expose proof verification as a standalone function that light clients can call
    /// directly, removing the executor from the trust path for sovereign cells entirely.
    ///
    /// Verify a STARK execution proof for a sovereign cell and update its commitment.
    ///
    /// This is the core of Phase 3: proof-carrying sovereign turns. The executor
    /// does ZERO state manipulation — it only:
    /// 1. Retrieves the stored commitment
    /// 2. Verifies the STARK proof (public inputs bind old -> new commitment + effects hash)
    /// 3. Updates the 32-byte commitment
    ///
    /// Public inputs layout (Effect VM, 7+ BabyBear elements):
    ///   [old_commit(1), new_commit(1), net_delta_mag(1), net_delta_sign(1),
    ///    effects_hash_lo(1), effects_hash_hi(1), custom_count(1),
    ///    ...custom_entries(8 per custom effect)]
    pub(super) fn verify_and_commit_proof(
        &self,
        cell_id: &CellId,
        proof_bytes: &[u8],
        turn: &Turn,
        ledger: &mut Ledger,
    ) -> Result<(), TurnError> {
        // THE ROTATION (cutover C1): the matched producer
        // (`sdk::cipherclerk::execute_sovereign_turn_with_proof`) mints a rotated
        // R=24 `Ir2BatchProof` over the cohort descriptor, carrying the v9 felt
        // commitment. When that producer is compiled (native default,
        // `dregg-circuit/prover`), verify through `verify_vm_descriptor2` (the
        // multi-table batch verifier), NOT the weak hand-AIR `EffectVmAir`. The
        // rotated wire is a postcard-serialized `BatchProof` (no `DREG` magic), so
        // it would (correctly) fail the v1 `stark::proof_from_bytes` — the two
        // halves move together.
        #[cfg(feature = "prover")]
        {
            self.verify_and_commit_proof_rotated(cell_id, proof_bytes, turn, ledger)
        }
        #[cfg(not(feature = "prover"))]
        {
            self.verify_and_commit_proof_v1(cell_id, proof_bytes, turn, ledger)
        }
    }

    /// THE ROTATED sovereign verify (cutover C1, decision #1's verify leg). The
    /// proof is a rotated R=24 `Ir2BatchProof` minted by
    /// `sdk::cipherclerk::execute_sovereign_turn_with_proof` over the cohort
    /// descriptor for the turn's effect. We RECONSTRUCT the exact 38-PI vector the
    /// prover bound and verify through `descriptor_ir2::verify_vm_descriptor2` — the
    /// multi-table batch verifier — retiring the weaker hand-AIR `EffectVmAir` leg.
    ///
    /// PI reconstruction (all 38 must match the prover for Fiat–Shamir to agree):
    ///   * PIs 0..33 (the v1 sub-trace prefix) + PI 37 (the caveat commit) are
    ///     witness-INDEPENDENT — they are a function of `(initial_vm_state,
    ///     vm_effects, caveat)` alone, so a re-run of `generate_rotated_effect_vm_trace`
    ///     with PLACEHOLDER block witnesses reproduces them exactly;
    ///   * PI 34 (rotated OLD commit) ← the stored sovereign v9 commitment felt;
    ///   * PI 35 (rotated NEW commit) ← `turn.execution_proof_new_commitment` felt
    ///     (the claimed post-state; the descriptor's `pi_binding` at col 261 ties it
    ///     to the trace's after-block `STATE_COMMIT`, so a forged claim is rejected);
    ///   * PI 36 (committed height) ← the cell's own committed height.
    ///
    /// The verifier does NOT reconstruct the producer's turn-context (`cells_root` /
    /// `iroot`): those are absorbed INTO the v9 commitment, which the proof binds and
    /// the verifier takes from trusted storage/claim. A tampered post-state commitment
    /// makes PI 35 disagree with the trace's bound carrier ⇒ UNSAT (the anti-ghost
    /// tooth, exercised in `tests/src/sovereign_proof.rs`).
    #[cfg(feature = "prover")]
    pub(super) fn verify_and_commit_proof_rotated(
        &self,
        cell_id: &CellId,
        proof_bytes: &[u8],
        turn: &Turn,
        ledger: &mut Ledger,
    ) -> Result<(), TurnError> {
        use crate::rotation_witness::{NUM_PRE_LIMBS, committed_height_felt};
        use dregg_circuit::descriptor_ir2::{
            DreggStarkConfig, Ir2BatchProof, parse_vm_descriptor2, verify_vm_descriptor2,
        };
        use dregg_circuit::effect_vm::trace_rotated::{
            RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_trace,
            generate_rotated_effect_vm_trace_with_fee, rotated_descriptor_name_for_effect,
            rotated_descriptor_name_for_effect_fee, transfer_caveat_manifest,
        };
        use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
        use dregg_circuit::field::BabyBear;

        // 1. Stored sovereign commitment (the v9 felt the matched producer wrote).
        let old_commitment = if let Some(c) = ledger.get_sovereign_commitment(cell_id) {
            *c
        } else if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
            reg.commitment
        } else {
            return Err(TurnError::SovereignNotRegistered { cell: *cell_id });
        };
        let new_commitment = turn.execution_proof_new_commitment.ok_or_else(|| {
            TurnError::InvalidExecutionProof(
                "execution_proof_new_commitment is required".to_string(),
            )
        })?;

        // 2. Deserialize the rotated `Ir2BatchProof` (postcard; no `DREG` magic).
        let ir2_proof: Ir2BatchProof<DreggStarkConfig> = postcard::from_bytes(proof_bytes)
            .map_err(|e| {
                TurnError::InvalidExecutionProof(format!("rotated proof deserialize: {e}"))
            })?;

        // 3. Reconstruct the circuit pre-state + VM effects from the before-cell the
        //    ledger holds (the SAME construction the producer used).
        let cell = ledger.get(cell_id).ok_or_else(|| {
            TurnError::InvalidExecutionProof(format!(
                "rotated verify: sovereign cell {cell_id} not present in the ledger"
            ))
        })?;
        // UNDO PHASE 1 (`execute.rs` PHASE 1, "Commit fee + nonce"): by the time this
        // verifier runs the executor has ALREADY debited `turn.fee` from the agent cell's
        // balance and incremented its nonce. The matched producer proved against the
        // PRE-fee, PRE-increment state (the cipherclerk's sovereign cell), so we reconstruct
        // that state to reproduce the v1 sub-trace's init/final balance + nonce PIs. The
        // reconstruction's correctness is cross-checked by OLD_COMMIT (PI 34): if our
        // pre-state diverges from the producer's, PI 34 ≠ the stored sovereign commitment.
        let cap_root = dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities);
        let post_fee_balance = cell.state.balance();
        let pre_balance =
            u64::try_from(post_fee_balance.saturating_add(turn.fee as i64)).map_err(|_| {
                TurnError::InvalidExecutionProof(
                    "rotated verify: cell balance is negative".to_string(),
                )
            })?;
        let pre_nonce = (cell.state.nonce().saturating_sub(1)) as u32;
        let cell_committed_height = cell.state.committed_height();
        // P0-2 (commit `548ac920a`): the deployed commitment now binds the FULL kernel — the
        // circuit `record_digest` aux column is seeded from the cell's authority residue
        // (`compute_authority_digest_felt`), NOT the cell-independent `empty_record_digest()`.
        // The producer seeds this same digest (`cipherclerk::prove_sovereign_turn_rotated`'s
        // `with_capability_root_and_record_digest`), so the verifier MUST reproduce it to
        // regenerate the identical trace + PI vector — otherwise the Fiat–Shamir transcript
        // diverges and the FRI proof-of-work witness is rejected (`InvalidPowWitness`).
        let record_digest = dregg_cell::compute_authority_digest_felt(cell);
        let initial_vm_state =
            dregg_circuit::CellState::with_capability_root_and_record_digest(
                pre_balance,
                pre_nonce,
                cap_root,
                record_digest,
            );
        let vm_effects = convert_turn_effects_to_vm(cell_id, turn);

        // 4. Resolve the cohort descriptor by the turn's lead effect (the SAME resolver
        //    the producer used). A non-cohort effect fails closed.
        let lead = vm_effects.first().ok_or_else(|| {
            TurnError::InvalidExecutionProof("rotated verify: empty effect set".to_string())
        })?;
        // FEE-IN-PROOF (the `transferFeeVmDescriptor2R24` route): a plain sovereign `Transfer` lead
        // routes the fee-aware descriptor (39 PIs) where the fee is debited INSIDE the proven
        // transition — the producer (`cipherclerk::prove_sovereign_turn_rotated`) routes the SAME
        // descriptor via `rotated_descriptor_name_for_effect_fee`. The fee is a PUBLISHED PI (slot 38)
        // the verifier sets from `turn.fee`, and the proof's gate FORCES the after-balance =
        // pre − transfer − fee, so a forged / underclaimed fee is UNSAT. We retire the old blind
        // `pre_balance = post_fee_balance + turn.fee` after-state reconstruction for the proven
        // transition (it survives ONLY for the pre-fee BEFORE/OLD_COMMIT block, below).
        let is_fee_transfer =
            matches!(vm_effects.as_slice(), [dregg_circuit::effect_vm::Effect::Transfer { .. }]);
        let name = if is_fee_transfer {
            rotated_descriptor_name_for_effect_fee(lead)
        } else {
            rotated_descriptor_name_for_effect(lead)
        }
        .ok_or_else(|| {
            TurnError::InvalidExecutionProof(format!(
                "rotated verify: effect {lead:?} is not in the R=24 rotated cohort"
            ))
        })?;
        let json = V3_STAGED_REGISTRY_TSV
            .lines()
            .find_map(|line| {
                let mut it = line.splitn(3, '\t');
                if it.next() == Some(name) {
                    let _name = it.next();
                    it.next()
                } else {
                    None
                }
            })
            .ok_or_else(|| {
                TurnError::InvalidExecutionProof(format!(
                    "rotated verify: {name} not in the staged rotated registry"
                ))
            })?;
        let desc = parse_vm_descriptor2(json).map_err(|e| {
            TurnError::InvalidExecutionProof(format!("rotated descriptor parse: {e}"))
        })?;

        // 5. The caveat manifest the producer used (transfer exercises both domains;
        //    everything else uses the empty manifest).
        let caveat = match vm_effects.as_slice() {
            [dregg_circuit::effect_vm::Effect::Transfer { .. }] => transfer_caveat_manifest(),
            _ => empty_caveat_manifest(),
        };

        // 6. Reconstruct the 38-PI vector. PLACEHOLDER block witnesses reproduce the
        //    witness-INDEPENDENT PIs (0..33 + 37) exactly; the commit/height PIs (34/35/36)
        //    are overridden from trusted storage/claim/cell below.
        let placeholder =
            RotatedBlockWitness::new(vec![BabyBear::ZERO; NUM_PRE_LIMBS], BabyBear::ZERO).map_err(
                |e| TurnError::InvalidExecutionProof(format!("rotated placeholder witness: {e}")),
            )?;
        let (_trace, mut dpis) = if is_fee_transfer {
            // Mirror the producer's fee-aware trace: the v1 sub-trace's after-balance is the PRE-fee
            // `before + amount·(1−2dir)` (from `initial_vm_state`'s pre-fee balance — reconstructed at
            // step 3 as `post_fee_balance + turn.fee`), and the fee generator debits `turn.fee` as the
            // SAME column override + commitment recompute the producer ran. PI 38 = `turn.fee` (the
            // generator writes it). The reconstructed post-fee after-block matches the producer's.
            generate_rotated_effect_vm_trace_with_fee(
                &initial_vm_state,
                &vm_effects,
                &placeholder,
                &placeholder,
                &caveat,
                turn.fee,
            )
        } else {
            generate_rotated_effect_vm_trace(
                &initial_vm_state,
                &vm_effects,
                &placeholder,
                &placeholder,
                &caveat,
            )
        }
        .map_err(|e| TurnError::InvalidExecutionProof(format!("rotated PI reconstruction: {e}")))?;
        if dpis.len() != desc.public_input_count {
            return Err(TurnError::InvalidExecutionProof(format!(
                "rotated verify: reconstructed {} PIs but descriptor wants {}",
                dpis.len(),
                desc.public_input_count
            )));
        }
        // OLD commit (PI 34) ← stored v9 felt; NEW (PI 35) ← claimed v9 felt; the
        // canonical single-felt encoding is the low-4-byte LE u32 (`felt_to_bytes32`),
        // read back as `BabyBear::new(u32)`.
        dpis[34] = BabyBear::new(u32::from_le_bytes(old_commitment[0..4].try_into().unwrap()));
        dpis[35] = BabyBear::new(u32::from_le_bytes(new_commitment[0..4].try_into().unwrap()));
        dpis[36] = committed_height_felt(cell_committed_height);
        // FEE-IN-PROOF: PI 38 is the PUBLISHED fee the col-89 last-row pin binds. Anchor it to the
        // TRUSTED `turn.fee` (the generator already wrote `BabyBear::new(turn.fee as u32)`, but we set
        // it explicitly so the published value is provably the turn's declared fee — a proof whose
        // bound col 89 disagrees with `turn.fee` is UNSAT). The gate then forces the after-balance
        // debit, retiring the verifier's blind `pre = post + fee` after-state reconstruction.
        if is_fee_transfer {
            dpis[38] = BabyBear::new(turn.fee as u32);
        }

        // 6b. THE RECORD-PIN ANCHOR (the deployment-soundness close for the record-digest family;
        // setPermissions BEACHHEAD). The record-pin descriptors ship at `public_input_count == 39`:
        // the descriptor's last-row pin (`EffectVmEmitRotationV3.rotateV3WithRecordPin`) welds the
        // AFTER block's `B_RECORD_DIGEST` limb (col 256) to rotated PI 38. The producer fills PI 38
        // from its honest after-cell's authority digest, but PI 38 is otherwise a FREE public input
        // the prover chooses — so the pin alone is a published-value binding, NOT a forcing gate,
        // UNTIL the verifier independently ANCHORS PI 38 to the trusted post-cell. We do that here:
        // clone the trusted before-cell (the SAME `cell` whose digest seeded the BEFORE `record_digest`
        // at PI reconstruction, cross-checked by OLD_COMMIT/PI 34), apply the lead effect through the
        // SHARED `apply_effect_to_cell` weld (the SAME projection the producer used for its after-cell —
        // any drift would reject HONEST proofs), and override PI 38 with the post-cell authority digest.
        // A forged after-permissions (a value the effect did NOT produce) makes this anchored PI 38
        // disagree with the proof's bound after-limb ⇒ `verify_vm_descriptor2` UNSAT ⇒ reject.
        //
        // ANCHORED — the FULL record-pin family (every effect whose descriptor ships at 39 PIs). Each
        // projects to its NATIVE VmEffect on BOTH the producer (`cipherclerk::convert_effects_to_vm`)
        // and the executor bridge (`convert_turn_effects_to_vm`), so the descriptor reconstructs
        // identically, and each MOVES its forced limb so a forged after-limb is UNSAT:
        //
        //   * RECORD-DIGEST limb 24 (`compute_authority_digest_felt`): `SetPermissions` /
        //     `SetVerificationKey` (permissions / vk.hash folded into r23) AND `Refusal` (the deployed
        //     `apply_refusal` now writes the audit into the EXT `fields_root`, which
        //     `compute_authority_digest_felt` folds — `REFUSAL_AUDIT_EXT_KEY`).
        //   * LIFECYCLE limb 29 (`lifecycle_felt_cell`): `CellSeal` / `CellUnseal` / `CellDestroy` (the
        //     lifecycle separates Live/Sealed/Destroyed + folds the death-cert) AND `ReceiptArchive`
        //     (the deployed `apply_receipt_archive` moves the lifecycle to `Archived`; the pin is
        //     re-routed to `B_LIFECYCLE` to match the deployed apply).
        //
        // A forged after-limb (a value the effect did NOT produce) makes the anchored PI 38 disagree
        // with the proof's bound forced column ⇒ `verify_vm_descriptor2` UNSAT. The whole record-pin
        // family is now a genuine forcing gate on the deployed path.
        if desc.public_input_count == 39 && dpis.len() == 39 {
            use dregg_circuit::effect_vm::Effect as VmEffect;
            // The forced-limb anchor flavor for this lead: record-digest (Class-1) vs lifecycle (Class-2).
            enum Anchor {
                None,
                RecordDigest,
                Lifecycle,
            }
            let anchor = match lead {
                VmEffect::SetPermissions { .. }
                | VmEffect::SetVerificationKey { .. }
                | VmEffect::Refusal { .. } => Anchor::RecordDigest,
                VmEffect::CellSeal { .. }
                | VmEffect::CellUnseal { .. }
                | VmEffect::CellDestroy { .. }
                | VmEffect::ReceiptArchive { .. } => Anchor::Lifecycle,
                _ => Anchor::None,
            };
            if !matches!(anchor, Anchor::None) {
                // Recover the kernel effect (the lead VmEffect only carries a hash). `dfs_collect_effects`
                // walks the call forest in the SAME order as `convert_turn_effects_to_vm`, so the first
                // matching record-pin effect targeting this cell is the lead's kernel pre-image.
                let lead_effect = Self::dfs_collect_effects(turn).into_iter().find(|e| {
                    matches!(e, Effect::SetPermissions { cell, .. } if cell == cell_id)
                        || matches!(e, Effect::SetVerificationKey { cell, .. } if cell == cell_id)
                        || matches!(e, Effect::Refusal { cell, .. } if cell == cell_id)
                        || matches!(e, Effect::CellSeal { target, .. } if target == cell_id)
                        || matches!(e, Effect::CellUnseal { target } if target == cell_id)
                        || matches!(e, Effect::CellDestroy { target, .. } if target == cell_id)
                        || matches!(e, Effect::ReceiptArchive { checkpoint, .. } if checkpoint.cell_id == *cell_id)
                });
                if let Some(lead_effect) = lead_effect {
                    let mut post_cell = cell.clone();
                    crate::rotation_witness::apply_effect_to_cell(
                        &mut post_cell,
                        cell_id,
                        &lead_effect,
                        self.block_height,
                    );
                    dpis[38] = match anchor {
                        Anchor::RecordDigest => {
                            dregg_cell::compute_authority_digest_felt(&post_cell)
                        }
                        Anchor::Lifecycle => {
                            crate::rotation_witness::lifecycle_felt_cell(&post_cell)
                        }
                        Anchor::None => unreachable!(),
                    };
                }
            }
        }

        // 7. Verify through the multi-table batch verifier (the hand-AIR leg is gone).
        verify_vm_descriptor2(&desc, &ir2_proof, &dpis).map_err(|e| {
            // A post-state forgery surfaces here: PI 35 disagrees with the trace's
            // after-block STATE_COMMIT carrier (the descriptor's col-261 pi_binding).
            TurnError::ProofVerificationFailed(format!("rotated effect-vm verify: {e}"))
        })?;

        // 8. Update commitment (legacy map first, then registrations) — unchanged.
        if ledger.is_sovereign(cell_id) {
            let _ = ledger.update_sovereign_commitment(cell_id, new_commitment);
        } else {
            let _ = ledger.update_sovereign_registration_commitment(
                cell_id,
                old_commitment,
                new_commitment,
                self.block_height,
            );
        }
        Ok(())
    }

    /// RETIRED (v1 hand-AIR sovereign verify): the `EffectVmAir` verify+commit leg is
    /// gone. The live path verifies sovereign transitions through the rotated
    /// proof-carrying turn (`verify_and_commit_proof` → `verify_and_commit_proof_rotated`,
    /// `prover`-gated). On a `not(prover)` build the sovereign verify fails closed.
    #[cfg(not(feature = "prover"))]
    pub(super) fn verify_and_commit_proof_v1(
        &self,
        cell_id: &CellId,
        proof_bytes: &[u8],
        turn: &Turn,
        _ledger: &mut Ledger,
    ) -> Result<(), TurnError> {
        let _ = (cell_id, proof_bytes, turn);
        Err(TurnError::InvalidExecutionProof(
            "v1 hand-AIR sovereign verify is retired; sovereign transitions verify through the \
             rotated proof-carrying turn"
                .to_string(),
        ))
    }

    /// RETIRED (v1 sovereign-witness STARK verify): the `EffectVmAir` witness-STARK verify
    /// is gone. The recursion tower verifies sovereign transitions through the rotated
    /// proof-carrying turn; a v1 `transition_proof` is rejected at the `execute.rs` call
    /// site rather than verified here.
    #[cfg(not(feature = "prover"))]
    pub(super) fn verify_sovereign_witness_stark(
        &self,
        _cell_id: &CellId,
        old_commitment: &[u8; 32],
        new_commitment: &[u8; 32],
        effects_hash: &[u8; 32],
        proof_bytes: &[u8],
    ) -> Result<(), TurnError> {
        let _ = (old_commitment, new_commitment, effects_hash, proof_bytes);
        Err(TurnError::InvalidExecutionProof(
            "v1 sovereign-witness STARK verify is retired; sovereign transitions verify through \
             the rotated proof-carrying turn"
                .to_string(),
        ))
    }

    /// Stage 7-γ.0d: cross-proof PI matching for a bundle of per-cell proofs
    /// from one turn.
    ///
    /// Given the N per-cell proof PI vectors that a turn's bundle has
    /// produced (one entry per touched cell, in any order), enforces that
    /// all of them agree on the four "turn-identity" PI fields introduced
    /// at γ.0a:
    ///
    ///   - PI[TURN_HASH_BASE..+4]
    ///   - PI[EFFECTS_HASH_GLOBAL_BASE..+4]
    ///   - PI[ACTOR_NONCE]
    ///   - PI[PREVIOUS_RECEIPT_HASH_BASE..+4]
    ///
    /// Also enforces — if `turn` is provided — that the shared values
    /// match the canonical `Turn::hash`-derived projection
    /// (`compute_turn_identity_pi`). This second check is the
    /// executor-side enforcement that γ.0 keeps trusted; γ.1 will move
    /// the `effects_hash_global ↔ Σ effects_local` direction into an
    /// aggregation micro-AIR.
    ///
    /// Per-proof STARK verification is the caller's responsibility (see
    /// `verify_and_commit_proof` for the single-cell case). This function
    /// only checks PI consistency across the bundle and against the turn.
    ///
    /// Returns `Ok(())` if every PI vector in `bundle_pis` agrees with
    /// every other on the four shared slots and (when `turn.is_some()`)
    /// with the canonical projection.
    pub fn verify_proof_carrying_turn_bundle(
        bundle_pis: &[Vec<dregg_circuit::field::BabyBear>],
        turn: Option<&Turn>,
    ) -> Result<(), TurnError> {
        use dregg_circuit::effect_vm::pi;
        use dregg_circuit::field::BabyBear;

        if bundle_pis.is_empty() {
            return Ok(());
        }

        // Every PI vector must be at least as long as the active PI layout —
        // shorter vectors can't carry the γ.0a slots or the v3 tail at all.
        for (i, p) in bundle_pis.iter().enumerate() {
            if p.len() < pi::ACTIVE_BASE_COUNT {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bundle proof {} has {} public inputs, expected at least {} \
                     (PI v3 layout)",
                    i,
                    p.len(),
                    pi::ACTIVE_BASE_COUNT
                )));
            }
        }

        // Determine the canonical "shared" values. When the turn is
        // supplied, use Turn::compute_turn_identity_pi (executor-trusted
        // source of truth). Otherwise, take the first proof's values as
        // the reference and verify the rest match — useful for federation
        // verifiers that receive a bundle without re-deriving the Turn.
        let (ref_turn_hash, ref_eff_global, ref_actor_nonce, ref_prev_receipt): (
            [BabyBear; 4],
            [BabyBear; 4],
            BabyBear,
            [BabyBear; 4],
        ) = if let Some(t) = turn {
            let (th, eg, an, pr) = Self::compute_turn_identity_pi(t);
            (th, eg, BabyBear::new((an & 0x7FFF_FFFF) as u32), pr)
        } else {
            let p0 = &bundle_pis[0];
            let mut th = [BabyBear::ZERO; 4];
            let mut eg = [BabyBear::ZERO; 4];
            let mut pr = [BabyBear::ZERO; 4];
            th.copy_from_slice(&p0[pi::TURN_HASH_BASE..(pi::TURN_HASH_BASE + 4)]);
            eg.copy_from_slice(
                &p0[pi::EFFECTS_HASH_GLOBAL_BASE..(pi::EFFECTS_HASH_GLOBAL_BASE + 4)],
            );
            pr.copy_from_slice(
                &p0[pi::PREVIOUS_RECEIPT_HASH_BASE..(pi::PREVIOUS_RECEIPT_HASH_BASE + 4)],
            );
            (th, eg, p0[pi::ACTOR_NONCE], pr)
        };

        // Per-proof check: each proof must agree with the reference on
        // every shared slot. Errors name the slot and the proof index.
        for (proof_idx, p) in bundle_pis.iter().enumerate() {
            for i in 0..pi::TURN_HASH_LEN {
                if p[pi::TURN_HASH_BASE + i] != ref_turn_hash[i] {
                    return Err(TurnError::InvalidExecutionProof(format!(
                        "bundle PI mismatch: TURN_HASH felt {} differs in proof {} \
                         (expected {:?}, got {:?})",
                        i,
                        proof_idx,
                        ref_turn_hash[i],
                        p[pi::TURN_HASH_BASE + i],
                    )));
                }
            }
            for i in 0..pi::EFFECTS_HASH_GLOBAL_LEN {
                if p[pi::EFFECTS_HASH_GLOBAL_BASE + i] != ref_eff_global[i] {
                    return Err(TurnError::InvalidExecutionProof(format!(
                        "bundle PI mismatch: EFFECTS_HASH_GLOBAL felt {} differs in \
                         proof {} (expected {:?}, got {:?})",
                        i,
                        proof_idx,
                        ref_eff_global[i],
                        p[pi::EFFECTS_HASH_GLOBAL_BASE + i],
                    )));
                }
            }
            if p[pi::ACTOR_NONCE] != ref_actor_nonce {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bundle PI mismatch: ACTOR_NONCE differs in proof {} \
                     (expected {:?}, got {:?})",
                    proof_idx,
                    ref_actor_nonce,
                    p[pi::ACTOR_NONCE],
                )));
            }
            for i in 0..pi::PREVIOUS_RECEIPT_HASH_LEN {
                if p[pi::PREVIOUS_RECEIPT_HASH_BASE + i] != ref_prev_receipt[i] {
                    return Err(TurnError::InvalidExecutionProof(format!(
                        "bundle PI mismatch: PREVIOUS_RECEIPT_HASH felt {} differs in \
                         proof {} (expected {:?}, got {:?})",
                        i,
                        proof_idx,
                        ref_prev_receipt[i],
                        p[pi::PREVIOUS_RECEIPT_HASH_BASE + i],
                    )));
                }
            }
        }

        // ---- Proof-to-action binding sweep §3.2/§3.3 + §5 ----
        //
        // If the turn carries sidecar effect-binding proofs (and/or
        // cross-effect dependencies and/or witness-index pins), run the
        // strong-soundness verification path on them. Turns without any
        // of these continue to apply with executor-trusted enforcement
        // (backwards compat); turns *with* them get the algebraic
        // full-fidelity check.
        if let Some(t) = turn {
            if !t.effect_binding_proofs.is_empty()
                || !t.cross_effect_dependencies.is_empty()
                || !t.effect_witness_index_map.is_empty()
            {
                // Without ledger snapshot: any Burn binding proof routes
                // through the snapshot-aware error path. Callers that need
                // Burn coverage must use
                // `verify_proof_carrying_turn_bundle_with_ledger`.
                Self::verify_effect_binding_proofs(t)?;
            }
        }

        Ok(())
    }

    /// Snapshot-aware variant of `verify_proof_carrying_turn_bundle`.
    /// Same shape, but threads a `&Ledger` into the binding-proof sweep so
    /// `SCHEMA_BURN` proofs can reconstruct `(old_balance, new_balance)`
    /// from the target cell's state. Closes AIR-SOUNDNESS-AUDIT #75.
    ///
    /// To avoid running the binding sweep twice (once snapshot-free,
    /// once snapshot-aware), this function temporarily clones the turn
    /// without its `effect_binding_proofs` and routes the cross-bundle
    /// PI check through that copy; then it issues the snapshot-aware
    /// binding-proof sweep against the original turn.
    pub fn verify_proof_carrying_turn_bundle_with_ledger(
        bundle_pis: &[Vec<dregg_circuit::field::BabyBear>],
        turn: Option<&Turn>,
        ledger: Option<&Ledger>,
    ) -> Result<(), TurnError> {
        // Run the cross-bundle PI checks via the existing path, with a
        // shallow clone that omits `effect_binding_proofs` so the
        // snapshot-free Burn arm is skipped. The other two
        // binding-extension fields (`cross_effect_dependencies` and
        // `effect_witness_index_map`) are ledger-independent and can
        // run either way; we drop all three from the clone and re-issue
        // the full sweep below with the snapshot-aware extractor.
        let stripped_turn: Option<Turn> = turn.map(|t| {
            let mut t = t.clone();
            t.effect_binding_proofs = Vec::new();
            t.cross_effect_dependencies = Vec::new();
            t.effect_witness_index_map = Vec::new();
            t
        });
        Self::verify_proof_carrying_turn_bundle(bundle_pis, stripped_turn.as_ref())?;
        if let Some(t) = turn {
            if !t.effect_binding_proofs.is_empty()
                || !t.cross_effect_dependencies.is_empty()
                || !t.effect_witness_index_map.is_empty()
            {
                Self::verify_effect_binding_proofs_with_ledger(t, ledger)?;
            }
        }
        Ok(())
    }

    /// Verify every sidecar `EffectBindingProof` carried by the turn.
    ///
    /// For each entry the verifier:
    ///   1. Locates the effect by `effect_index` (canonical DFS order
    ///      over the whole call_forest — same traversal as
    ///      `compute_turn_identity_pi`).
    ///   2. Looks up the schema by `schema_id`.
    ///   3. Reconstructs the expected PI vector from the executor's
    ///      view of the effect's typed parameters and compares it to
    ///      the proof's `public_inputs`.
    ///   4. STARK-verifies the proof against the reconstructed PI.
    ///
    /// Cross-effect dependencies are also enforced here: the chain
    /// pinning verifies that the producer effect's output field of
    /// the named type equals the consumer's input of the same type,
    /// preventing the executor from substituting a different value
    /// (e.g., a different nullifier) between producer and consumer in
    /// the same turn.
    ///
    /// Witness-blob → effect indexing entries are validated for
    /// well-formedness here; the AIR-side enforcement that the
    /// effect-claimed witness blob actually matches the indexed blob
    /// is the responsibility of the corresponding per-effect AIR (the
    /// generalized AIR exposes a `witness_blob_hash` schema slot when
    /// the binding schema declares one).
    pub fn verify_effect_binding_proofs(turn: &Turn) -> Result<(), TurnError> {
        // Backwards-compat wrapper: callers that don't have a ledger
        // snapshot (the `verify_proof_carrying_turn_bundle` static path,
        // and existing structural tests) route through here. The Burn
        // arm is the only schema whose executor-side projection requires
        // a snapshot (`old_balance`, `new_balance`); without one it
        // continues to surface as a schema/variant mismatch, the same
        // pre-AIR-#75 shape, so cleartext non-Burn turns are unaffected.
        Self::verify_effect_binding_proofs_with_ledger(turn, None)
    }

    /// Snapshot-aware variant. Pass `Some(ledger)` to wire the per-effect
    /// snapshot-dependent extractors (today: `SCHEMA_BURN`); pass `None`
    /// for the snapshot-free legacy behavior. Closes
    /// `AIR-SOUNDNESS-AUDIT.md` #75 by giving the Burn arm of
    /// `extract_binding_params` the pre/post ledger snapshot it needs
    /// to reconstruct `old_balance` / `new_balance` from `Effect::Burn`
    /// alone.
    pub fn verify_effect_binding_proofs_with_ledger(
        turn: &Turn,
        ledger: Option<&Ledger>,
    ) -> Result<(), TurnError> {
        use dregg_circuit::effect_action_air as eaa;
        use dregg_circuit::stark;

        // Build the canonical DFS-order effect list once, mirroring
        // `compute_turn_identity_pi`'s `dfs_collect`.
        let effects = Self::dfs_collect_effects(turn);

        // ---- 1) Effect binding proofs ----
        for (i, bp) in turn.effect_binding_proofs.iter().enumerate() {
            // Bounds-check effect_index.
            let eff = effects.get(bp.effect_index as usize).ok_or_else(|| {
                TurnError::InvalidExecutionProof(format!(
                    "effect_binding_proofs[{}]: effect_index {} out of range (have {} effects)",
                    i,
                    bp.effect_index,
                    effects.len()
                ))
            })?;

            // Resolve schema by id.
            let schema = Self::schema_by_id(&bp.schema_id).ok_or_else(|| {
                TurnError::InvalidExecutionProof(format!(
                    "effect_binding_proofs[{}]: unknown schema_id {:?}",
                    i, bp.schema_id
                ))
            })?;

            // Reconstruct expected (fields, amounts) from the executor's
            // view of the effect's typed parameters. Burn routes through
            // the snapshot-aware extractor; everything else uses the
            // snapshot-free path.
            let (exp_fields, exp_amounts) = if bp.schema_id == "dregg-effect-burn-v1" {
                Self::extract_burn_binding_params(eff, ledger).ok_or_else(|| {
                    TurnError::InvalidExecutionProof(format!(
                        "effect_binding_proofs[{}]: Burn binding requires a ledger \
                         snapshot to reconstruct (old_balance, new_balance); the \
                         caller did not provide one OR the effect at index {} is \
                         not an Effect::Burn / its target balance is not on the \
                         ledger",
                        i, bp.effect_index
                    ))
                })?
            } else {
                Self::extract_binding_params(eff, &bp.schema_id).ok_or_else(|| {
                    TurnError::InvalidExecutionProof(format!(
                        "effect_binding_proofs[{}]: effect at index {} does not match \
                         schema_id {:?} (schema/variant mismatch)",
                        i, bp.effect_index, bp.schema_id
                    ))
                })?
            };
            if exp_fields.len() != schema.field_count || exp_amounts.len() != schema.amount_count {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "effect_binding_proofs[{}]: schema {:?} expects {} fields + \
                     {} amounts, executor reconstruction got {} + {}",
                    i,
                    bp.schema_id,
                    schema.field_count,
                    schema.amount_count,
                    exp_fields.len(),
                    exp_amounts.len()
                )));
            }

            // Build the expected PI vector and check the wire PI agrees
            // (cheap byte-comparison rejection before STARK verify).
            let exp_pi_bb = {
                let w = eaa::EffectActionWitness {
                    schema,
                    fields: exp_fields.clone(),
                    amounts: exp_amounts.clone(),
                };
                w.public_inputs()
            };
            let bp_pi_bb = bp.public_inputs_babybear();
            if bp_pi_bb != exp_pi_bb {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "effect_binding_proofs[{}]: wire PI disagrees with executor's view \
                     of effect {} (schema {:?})",
                    i, bp.effect_index, bp.schema_id
                )));
            }

            // STARK-verify the proof against the reconstructed PI.
            let proof = stark::proof_from_bytes(&bp.proof_bytes).map_err(|e| {
                TurnError::InvalidExecutionProof(format!(
                    "effect_binding_proofs[{}]: deserialize: {}",
                    i, e
                ))
            })?;
            eaa::verify_effect_action(schema, &exp_fields, &exp_amounts, &proof).map_err(|e| {
                TurnError::ProofVerificationFailed(format!(
                    "effect_binding_proofs[{}] (schema {:?}, effect {}): {}",
                    i, bp.schema_id, bp.effect_index, e
                ))
            })?;
        }

        // ---- 2) Cross-effect within-turn chain pinning ----
        for (i, dep) in turn.cross_effect_dependencies.iter().enumerate() {
            if dep.producer_index >= dep.consumer_index {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "cross_effect_dependencies[{}]: producer_index {} must be < \
                     consumer_index {} (forward edges only)",
                    i, dep.producer_index, dep.consumer_index
                )));
            }
            let prod = effects.get(dep.producer_index as usize).ok_or_else(|| {
                TurnError::InvalidExecutionProof(format!(
                    "cross_effect_dependencies[{}]: producer_index {} out of range",
                    i, dep.producer_index
                ))
            })?;
            let cons = effects.get(dep.consumer_index as usize).ok_or_else(|| {
                TurnError::InvalidExecutionProof(format!(
                    "cross_effect_dependencies[{}]: consumer_index {} out of range",
                    i, dep.consumer_index
                ))
            })?;
            let prod_out =
                Self::extract_named_field_32b(prod, &dep.field_name).ok_or_else(|| {
                    TurnError::InvalidExecutionProof(format!(
                        "cross_effect_dependencies[{}]: producer effect has no \
                         output field {:?}",
                        i, dep.field_name
                    ))
                })?;
            let cons_in =
                Self::extract_named_field_32b(cons, &dep.field_name).ok_or_else(|| {
                    TurnError::InvalidExecutionProof(format!(
                        "cross_effect_dependencies[{}]: consumer effect has no \
                         input field {:?}",
                        i, dep.field_name
                    ))
                })?;
            if prod_out != dep.value_commit {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "cross_effect_dependencies[{}]: producer's {:?} disagrees with \
                     pinned value_commit",
                    i, dep.field_name
                )));
            }
            if cons_in != dep.value_commit {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "cross_effect_dependencies[{}]: consumer's {:?} disagrees with \
                     pinned value_commit (chain broken)",
                    i, dep.field_name
                )));
            }
        }

        // ---- 3) Witness-blob → Effect indexing ----
        //
        // Well-formedness only here: bounds-check effect_index. The
        // tighter AIR-side enforcement that the indexed blob's bytes
        // are the ones the effect's predicate dispatch consumes is
        // owned by the per-effect generalized AIR (witness_blob_hash
        // schema slot, when declared). Detecting duplicate
        // (effect_index, witness_index) pairs and unbound effects is
        // useful as an executor-side sanity check.
        let mut seen_effect_indices = std::collections::HashSet::new();
        for (i, ewi) in turn.effect_witness_index_map.iter().enumerate() {
            if effects.get(ewi.effect_index as usize).is_none() {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "effect_witness_index_map[{}]: effect_index {} out of range",
                    i, ewi.effect_index
                )));
            }
            if !seen_effect_indices.insert(ewi.effect_index) {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "effect_witness_index_map[{}]: duplicate effect_index {}",
                    i, ewi.effect_index
                )));
            }
        }

        Ok(())
    }

    /// Collect every Effect in the turn's call_forest in the canonical
    /// DFS-traversal order (same order as `compute_turn_identity_pi`).
    pub(super) fn dfs_collect_effects(turn: &Turn) -> Vec<Effect> {
        fn dfs(tree: &CallTree, out: &mut Vec<Effect>) {
            for effect in &tree.action.effects {
                out.push(effect.clone());
            }
            for child in &tree.children {
                dfs(child, out);
            }
        }
        let mut out = Vec::new();
        for root in &turn.call_forest.roots {
            dfs(root, &mut out);
        }
        out
    }

    /// Resolve an `EffectActionSchema` by its `schema_id` (the
    /// `kind_name` string used as the AIR's Fiat-Shamir domain
    /// separator). Returns `None` for unknown ids.
    pub(super) fn schema_by_id(
        id: &str,
    ) -> Option<dregg_circuit::effect_action_air::EffectActionSchema> {
        use dregg_circuit::effect_action_air as eaa;
        macro_rules! match_schemas {
            ($($s:ident),* $(,)?) => {
                $(
                    if id == eaa::$s.kind_name {
                        return Some(eaa::$s);
                    }
                )*
            };
        }
        match_schemas!(
            SCHEMA_GRANT_CAPABILITY,
            SCHEMA_REVOKE_CAPABILITY,
            SCHEMA_EMIT_EVENT,
            SCHEMA_CREATE_CELL,
            SCHEMA_SET_PERMISSIONS,
            SCHEMA_SET_VERIFICATION_KEY,
            SCHEMA_INTRODUCE,
            SCHEMA_REVOKE_DELEGATION,
            SCHEMA_SPAWN_WITH_DELEGATION,
            SCHEMA_EXERCISE_VIA_CAPABILITY,
            SCHEMA_PIPELINED_SEND,
            SCHEMA_CREATE_CELL_FROM_FACTORY,
            SCHEMA_NOTE_SPEND,
            SCHEMA_NOTE_CREATE,
            SCHEMA_BURN,
        );
        None
    }

    /// Reconstruct the (fields, amounts) tuple a given schema expects
    /// from the runtime `Effect`'s typed parameters. Returns `None`
    /// when the schema_id does not match the effect's variant (the
    /// caller's bug; a binding proof's schema must match its effect).
    ///
    /// This is the executor-side "what did the runtime variant
    /// actually carry?" projection that the binding proof's PI must
    /// match. Any drift between this projection and the prover's
    /// witness construction fails verification.
    pub(super) fn extract_binding_params(
        effect: &Effect,
        schema_id: &str,
    ) -> Option<(Vec<[u8; 32]>, Vec<u64>)> {
        match (schema_id, effect) {
            (
                "dregg-effect-note-spend-v1",
                Effect::NoteSpend {
                    nullifier,
                    note_tree_root,
                    value,
                    asset_type,
                    value_commitment,
                    ..
                },
            ) => {
                let asset_type_commit = {
                    let mut h = blake3::Hasher::new();
                    h.update(b"dregg-asset-type-commit/v1");
                    h.update(&asset_type.to_le_bytes());
                    *h.finalize().as_bytes()
                };
                let vc = value_commitment.unwrap_or([0u8; 32]);
                Some((
                    vec![nullifier.0, *note_tree_root, asset_type_commit, vc],
                    vec![*value, *asset_type],
                ))
            }
            (
                "dregg-effect-note-create-v1",
                Effect::NoteCreate {
                    commitment,
                    value,
                    asset_type,
                    value_commitment,
                    range_proof,
                    ..
                },
            ) => {
                let asset_type_commit = {
                    let mut h = blake3::Hasher::new();
                    h.update(b"dregg-asset-type-commit/v1");
                    h.update(&asset_type.to_le_bytes());
                    *h.finalize().as_bytes()
                };
                let vc = value_commitment.unwrap_or([0u8; 32]);
                let rph = match range_proof {
                    Some(bytes) => *blake3::hash(bytes).as_bytes(),
                    None => [0u8; 32],
                };
                Some((
                    vec![commitment.0, asset_type_commit, vc, rph],
                    vec![*value, *asset_type],
                ))
            }

            ("dregg-effect-revoke-delegation-v1", Effect::RevokeDelegation { child }) => {
                Some((vec![*child.as_bytes()], vec![]))
            }
            // SCHEMA_BURN (AIR-SOUNDNESS-AUDIT.md #75) is wired in
            // `extract_burn_binding_params` because it needs the pre/post
            // ledger snapshot (`old_balance`, `new_balance`) which this
            // snapshot-free extractor cannot reconstruct. The snapshot-
            // aware path is taken from
            // `verify_effect_binding_proofs_with_ledger` when the schema
            // id is `dregg-effect-burn-v1`; the snapshot-free path keeps
            // returning None here as a structural rejection so a Burn
            // binding proof can never silently slip through without
            // ledger context.
            ("dregg-effect-burn-v1", Effect::Burn { .. }) => None,
            // Other variants: extend as wire-in surface grows. Today
            // the lane closes NoteSpend/NoteCreate/BridgeLock at full
            // fidelity (the deferred §5 items); the remaining
            // schema_ids are valid for off-AIR construction but not
            // re-extracted by this executor-side projection. Add new
            // arms here as their executor-side projection is needed.
            _ => None,
        }
    }

    /// Snapshot-aware Burn binding parameter extractor (AIR-SOUNDNESS-AUDIT
    /// #75). `SCHEMA_BURN` has the field layout
    /// `fields = [target]`, `amounts = [old_balance, new_balance, amount,
    /// was_burn_flag]`. Of those, only `target` and `amount` are present on
    /// `Effect::Burn`; the executor-side projection reconstructs `old_balance`
    /// from the supplied ledger snapshot and `new_balance = old_balance -
    /// amount` (saturating at zero — runtime apply rejects underflow
    /// separately). `was_burn_flag` is always `1` for any Burn binding proof
    /// since the AIR enforces the disclosure bit. Returns `None` if `ledger`
    /// is `None`, if `effect` is not a `Burn`, or if the target cell is not
    /// in the ledger.
    pub(super) fn extract_burn_binding_params(
        effect: &Effect,
        ledger: Option<&Ledger>,
    ) -> Option<(Vec<[u8; 32]>, Vec<u64>)> {
        match effect {
            Effect::Burn {
                target,
                slot: _slot,
                amount,
            } => {
                let ledger = ledger?;
                let cell = ledger.get(target)?;
                // THE EPOCH §5: balances are SIGNED and cross the PI
                // boundary as the order-preserving BIASED u64
                // (`balance_biased`), which preserves differences —
                // `biased(old) - biased(new) = old - new` — so the AIR's
                // `new = old - amount` constraint shape is unchanged.
                // (Encoding touchpoint for the descriptor-regen lane.)
                let old_balance = cell.state.balance();
                // `new_balance` is the post-Burn balance. Underflow is
                // rejected by the executor's runtime `InsufficientBalance`
                // check before this code is reached; saturate at zero so an
                // off-AIR sanity test doesn't panic.
                let new_balance = old_balance.saturating_sub_unsigned(*amount).max(0);
                Some((
                    vec![*target.as_bytes()],
                    vec![
                        dregg_cell::state::balance_biased(old_balance),
                        dregg_cell::state::balance_biased(new_balance),
                        *amount,
                        1,
                    ],
                ))
            }
            _ => None,
        }
    }

    /// Extract a named 32-byte field from an Effect (for cross-effect
    /// chain pinning). Returns `None` when the effect doesn't carry a
    /// field of that name.
    pub(super) fn extract_named_field_32b(effect: &Effect, name: &str) -> Option<[u8; 32]> {
        match (name, effect) {
            ("nullifier", Effect::NoteSpend { nullifier, .. }) => Some(nullifier.0),

            ("nullifier", Effect::BridgeMint { portable_proof }) => Some(portable_proof.nullifier),
            ("note_commitment" | "commitment", Effect::NoteCreate { commitment, .. }) => {
                Some(commitment.0)
            }
            ("note_tree_root", Effect::NoteSpend { note_tree_root, .. }) => Some(*note_tree_root),

            _ => None,
        }
    }

    /// D5 (NoteSpend nullifier cross-binding, approach A): compute the
    /// expected `PI[NOTESPEND_NULLIFIER]` felt for `cell_id`'s EffectVM
    /// proof, or `None` when this cell's proof carries no NoteSpend row (the
    /// PI slot then stays at the ZERO sentinel).
    ///
    /// The returned felt is `fold_bytes32_to_bb(nullifier)`, matching the
    /// trace's `param0` for the first NoteSpend row. The nullifier is sourced
    /// from the TRUSTED side:
    ///   1. the turn's `SCHEMA_NOTE_SPEND` binding proof, if present (its
    ///      `fields[0]` is the certified nullifier — the value
    ///      `verify_effect_binding_proofs` STARK-verifies + PI-matches against
    ///      the spent note's preimage); failing that
    ///   2. the runtime NoteSpend effect's own nullifier (backwards compat).
    ///
    /// `vm_effects` is this cell's projected VM effect list (already folded);
    /// we use it only to detect whether a NoteSpend row exists for this cell
    /// and as the source for the felt we ultimately return, so the value is
    /// byte-identical to the trace's `param0`.
    ///
    /// V1-only: consumed exclusively by `verify_and_commit_proof_v1` (the rotated
    /// verifier reconstructs PIs from the trace generator, not these per-effect
    /// cross-binding helpers). Dead under `prover`; deleted with the v1 leg at C7.
    #[cfg_attr(feature = "prover", allow(dead_code))]
    fn expected_notespend_nullifier_bb(
        &self,
        _cell_id: &CellId,
        turn: &Turn,
        vm_effects: &[dregg_circuit::effect_vm::Effect],
    ) -> Option<dregg_circuit::field::BabyBear> {
        use dregg_circuit::effect_vm::{Effect as VmEffect, fold_bytes32_to_bb};

        // No NoteSpend row in this cell's proof → sentinel ZERO (None).
        // Mirror the trace generator: the PI slot binds the FIRST NoteSpend
        // row's folded nullifier (param0). The per-row AIR constraint forces
        // every NoteSpend row to share it.
        let runtime_fold = vm_effects.iter().find_map(|e| match e {
            VmEffect::NoteSpend { nullifier, .. } => Some(*nullifier),
            _ => None,
        })?;

        // Prefer the binding-proof-certified nullifier. Walk the turn's
        // SCHEMA_NOTE_SPEND binding proofs; for the first that references an
        // Effect::NoteSpend, fold its certified `nullifier.0` (== fields[0]
        // per `extract_binding_params`). Because the binding-proof sweep
        // (`verify_effect_binding_proofs`) independently STARK-verifies and
        // PI-matches that proof against this same nullifier, sourcing it here
        // welds the EffectVM param0 to the spending proof's certified value.
        let effects = Self::dfs_collect_effects(turn);
        for bp in &turn.effect_binding_proofs {
            if bp.schema_id != "dregg-effect-note-spend-v1" {
                continue;
            }
            if let Some(eff) = effects.get(bp.effect_index as usize) {
                if let Some(nullifier_32) = Self::extract_named_field_32b(eff, "nullifier") {
                    if matches!(eff, Effect::NoteSpend { .. }) {
                        return Some(fold_bytes32_to_bb(&nullifier_32));
                    }
                }
            }
        }

        // No binding proof: fall back to the runtime fold (already byte-
        // identical to the trace's param0).
        Some(runtime_fold)
    }

    /// D5b (NoteCreate commitment cross-binding, approach A): compute the
    /// expected `PI[NOTECREATE_COMMITMENT]` felt, or `None` when this cell's
    /// proof carries no NoteCreate row. The returned felt is
    /// `fold_bytes32_to_bb(commitment)`, matching the trace's NoteCreate
    /// `param0`. Sourced from the TRUSTED side:
    ///   1. the turn's `SCHEMA_NOTE_CREATE` binding proof, if present (its
    ///      `fields[0]` is the certified commitment that
    ///      `verify_effect_binding_proofs` STARK-verifies + PI-matches against
    ///      its value/asset/range opening); failing that
    ///   2. the runtime NoteCreate effect's own commitment (backwards compat).
    #[cfg_attr(feature = "prover", allow(dead_code))]
    fn expected_notecreate_commitment_bb(
        &self,
        turn: &Turn,
        vm_effects: &[dregg_circuit::effect_vm::Effect],
    ) -> Option<dregg_circuit::field::BabyBear> {
        use dregg_circuit::effect_vm::{Effect as VmEffect, fold_bytes32_to_bb};

        // No NoteCreate row in this cell's proof → sentinel ZERO (None).
        let runtime_fold = vm_effects.iter().find_map(|e| match e {
            VmEffect::NoteCreate { commitment, .. } => Some(*commitment),
            _ => None,
        })?;

        // Prefer the binding-proof-certified commitment (fields[0] ==
        // commitment.0 per `extract_binding_params` for note-create).
        let effects = Self::dfs_collect_effects(turn);
        for bp in &turn.effect_binding_proofs {
            if bp.schema_id != "dregg-effect-note-create-v1" {
                continue;
            }
            if let Some(eff) = effects.get(bp.effect_index as usize) {
                if matches!(eff, Effect::NoteCreate { .. }) {
                    if let Some(commitment_32) = Self::extract_named_field_32b(eff, "commitment") {
                        return Some(fold_bytes32_to_bb(&commitment_32));
                    }
                }
            }
        }

        Some(runtime_fold)
    }

    /// D5c (Burn target cross-binding, approach A): compute the expected
    /// `PI[BURN_TARGET_PI]` felt, or `None` when this cell's proof carries no
    /// Burn row. The returned felt is `fold_bytes32_to_bb(target.as_bytes())`,
    /// matching the trace's Burn `param0`. Sourced from the TRUSTED side:
    ///   1. the turn's `SCHEMA_BURN` binding proof, if present (its `fields[0]`
    ///      is the certified target — the cell whose `old - new == amount`
    ///      balance arithmetic `verify_effect_binding_proofs_with_ledger`
    ///      validates against the ledger snapshot); failing that
    ///   2. the runtime Burn effect's own target (backwards compat).
    #[cfg_attr(feature = "prover", allow(dead_code))]
    fn expected_burn_target_bb(
        &self,
        turn: &Turn,
        vm_effects: &[dregg_circuit::effect_vm::Effect],
    ) -> Option<dregg_circuit::field::BabyBear> {
        use dregg_circuit::effect_vm::{Effect as VmEffect, fold_bytes32_to_bb};

        // No Burn row in this cell's proof → sentinel ZERO (None).
        let runtime_fold = vm_effects.iter().find_map(|e| match e {
            VmEffect::Burn { target_hash, .. } => Some(*target_hash),
            _ => None,
        })?;

        // Prefer the binding-proof-certified target. SCHEMA_BURN fields[0] ==
        // `*target.as_bytes()` per `extract_burn_binding_params`; fold it with
        // the SAME `fold_bytes32_to_bb` the bridge uses
        // (`hash_to_bb(target.as_bytes())`), so the value is byte-identical to
        // the trace's Burn param0.
        let effects = Self::dfs_collect_effects(turn);
        for bp in &turn.effect_binding_proofs {
            if bp.schema_id != "dregg-effect-burn-v1" {
                continue;
            }
            if let Some(Effect::Burn { target, .. }) = effects.get(bp.effect_index as usize) {
                return Some(fold_bytes32_to_bb(target.as_bytes()));
            }
        }

        Some(runtime_fold)
    }

    /// Stage 7-γ.2 Phase 1: bilateral cross-cell PI consistency check.
    ///
    /// Given a turn and the bundle of per-cell `(cell_id, PI)` pairs, this
    /// reconstructs the expected bilateral schedule from `call_forest +
    /// ACTOR_NONCE` and verifies that each per-cell PI's bilateral count
    /// fields and accumulator-root fields match what the schedule predicts.
    ///
    /// It also enforces the `IS_AGENT_CELL` rule: at most one proof in the
    /// bundle carries `PI[IS_AGENT_CELL] == 1`, and if any does it must be
    /// the cell named in `turn.agent`. All other proofs must have
    /// `PI[IS_AGENT_CELL] == 0`.
    ///
    /// Closes the threats from `EXECUTOR-HONESTY-AUDIT.md` T1 (sender lies
    /// about outbound transfer), T3 (intro permission tampering across
    /// sides), T15 multi-cell tails. See `STAGE-7-GAMMA-2-PI-DESIGN.md` §4.
    pub fn verify_bilateral_bundle(
        bundle: &[(dregg_types::CellId, Vec<dregg_circuit::field::BabyBear>)],
        turn: &Turn,
    ) -> Result<(), TurnError> {
        use crate::bilateral_schedule::ExpectedBilateral;
        let schedule = ExpectedBilateral::from_turn(turn);
        Self::verify_bilateral_bundle_with_schedule(bundle, turn, &schedule)
    }

    /// γ.2 unilateral binding extension: same as [`verify_bilateral_bundle`]
    /// but takes a pre-built `ExpectedBilateral` so the caller can populate
    /// `unilateral_attestations` (which cannot be derived from `call_forest`
    /// alone — they're per-cell self-witnessing data that lives outside the
    /// Turn).
    ///
    /// Use this when a sovereign cell / peer_exchange transition carries
    /// unilateral attestations that must be cross-checked against the PI
    /// accumulator. Callers that don't have unilateral attestations can
    /// keep using [`verify_bilateral_bundle`] — it builds an empty
    /// unilateral list, which produces sentinel roots / zero counts.
    pub fn verify_bilateral_bundle_with_schedule(
        bundle: &[(dregg_types::CellId, Vec<dregg_circuit::field::BabyBear>)],
        turn: &Turn,
        schedule: &crate::bilateral_schedule::ExpectedBilateral,
    ) -> Result<(), TurnError> {
        use crate::bilateral_schedule::extract_from_pi;
        use dregg_circuit::effect_vm::pi;

        if bundle.is_empty() {
            return Ok(());
        }

        // Reject any per-cell PI that's too short to carry the active layout.
        for (i, (cid, p)) in bundle.iter().enumerate() {
            if p.len() < pi::ACTIVE_BASE_COUNT {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral bundle entry {} (cell {:?}) has {} public \
                     inputs, expected at least {} (PI v3 layout)",
                    i,
                    cid,
                    p.len(),
                    pi::ACTIVE_BASE_COUNT
                )));
            }
        }

        let actor_nonce = turn.nonce;

        // Per-cell check.
        let mut agent_count = 0usize;
        for (idx, (cell_id, p)) in bundle.iter().enumerate() {
            let (counts, roots) = extract_from_pi(p);
            let expected_counts = schedule.counts_for(cell_id);
            let expected_roots = schedule.roots_for(cell_id, actor_nonce);

            macro_rules! count_check {
                ($field:ident, $name:literal) => {
                    if counts.$field != expected_counts.$field {
                        return Err(TurnError::InvalidExecutionProof(format!(
                            "bilateral PI mismatch in proof {} (cell {:?}): \
                             {} expected {} got {}",
                            idx, cell_id, $name, expected_counts.$field, counts.$field
                        )));
                    }
                };
            }
            count_check!(outbound_transfer, "outbound_transfer_count");
            count_check!(inbound_transfer, "inbound_transfer_count");
            count_check!(outbound_grant, "outbound_grant_count");
            count_check!(inbound_grant, "inbound_grant_count");
            count_check!(intro_as_introducer, "intro_as_introducer_count");
            count_check!(intro_as_recipient, "intro_as_recipient_count");
            count_check!(intro_as_target, "intro_as_target_count");
            // γ.2 unilateral binding: per-cell self-attestation count.
            count_check!(unilateral_attestations, "unilateral_attestations_count");

            macro_rules! root_check {
                ($field:ident, $name:literal) => {
                    if roots.$field != expected_roots.$field {
                        return Err(TurnError::InvalidExecutionProof(format!(
                            "bilateral PI mismatch in proof {} (cell {:?}): \
                             {} root differs from schedule",
                            idx, cell_id, $name
                        )));
                    }
                };
            }
            root_check!(outgoing_transfer, "outgoing_transfer");
            root_check!(incoming_transfer, "incoming_transfer");
            root_check!(outgoing_grant, "outgoing_grant");
            root_check!(incoming_grant, "incoming_grant");
            root_check!(intro_as_introducer, "intro_as_introducer");
            root_check!(intro_as_recipient, "intro_as_recipient");
            root_check!(intro_as_target, "intro_as_target");
            // γ.2 unilateral binding: per-cell self-attestation accumulator root.
            root_check!(unilateral_attestations, "unilateral_attestations");

            // IS_AGENT_CELL consistency.
            let is_agent = p[pi::IS_AGENT_CELL];
            let is_agent_u = is_agent.as_u32();
            if is_agent_u != 0 && is_agent_u != 1 {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral PI in proof {} (cell {:?}): IS_AGENT_CELL must be 0 or 1, got {}",
                    idx, cell_id, is_agent_u
                )));
            }
            let should_be_agent = cell_id == &turn.agent;
            if should_be_agent && is_agent_u != 1 {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral PI in proof {} (cell {:?}): cell is the turn.agent \
                     but IS_AGENT_CELL == 0",
                    idx, cell_id
                )));
            }
            if !should_be_agent && is_agent_u != 0 {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral PI in proof {} (cell {:?}): cell is NOT the turn.agent \
                     but IS_AGENT_CELL == 1",
                    idx, cell_id
                )));
            }
            if is_agent_u == 1 {
                agent_count += 1;
            }
        }

        // Exactly-one-agent rule: at most one proof should claim agent.
        if agent_count > 1 {
            return Err(TurnError::InvalidExecutionProof(format!(
                "bilateral bundle has {} proofs claiming IS_AGENT_CELL == 1; \
                 at most one allowed",
                agent_count
            )));
        }

        // Cross-side existence check: every Transfer / Grant in the
        // schedule should have *both* its endpoints represented in the
        // bundle whenever either appears. If one side appears but the peer
        // does not, that's a hard reject — the bundle is incomplete
        // relative to the schedule, and a malicious prover could otherwise
        // produce only the side that benefits them.
        let covered: std::collections::HashSet<&dregg_types::CellId> =
            bundle.iter().map(|(c, _)| c).collect();
        for t in &schedule.transfers {
            let from_in = covered.contains(&t.from);
            let to_in = covered.contains(&t.to);
            if from_in != to_in {
                let missing = if from_in { &t.to } else { &t.from };
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral schedule references both {:?} and {:?} in a Transfer \
                     but bundle only covers one; missing peer {:?}",
                    t.from, t.to, missing
                )));
            }
        }
        for g in &schedule.grants {
            let from_in = covered.contains(&g.from);
            let to_in = covered.contains(&g.to);
            if from_in != to_in {
                let missing = if from_in { &g.to } else { &g.from };
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral schedule references both {:?} and {:?} in a Grant \
                     but bundle only covers one; missing peer {:?}",
                    g.from, g.to, missing
                )));
            }
        }
        for intro in &schedule.introduces {
            let any_covered = covered.contains(&intro.introducer)
                || covered.contains(&intro.recipient)
                || covered.contains(&intro.target);
            if any_covered {
                let distinct: std::collections::HashSet<&dregg_types::CellId> =
                    [&intro.introducer, &intro.recipient, &intro.target]
                        .into_iter()
                        .collect();
                for c in &distinct {
                    if !covered.contains(*c) {
                        return Err(TurnError::InvalidExecutionProof(format!(
                            "bilateral schedule references Introduce({:?}, {:?}, {:?}) \
                             but bundle is missing role-player {:?}",
                            intro.introducer, intro.recipient, intro.target, c
                        )));
                    }
                }
            }
        }

        Ok(())
    }

    /// Convenience: verify a bundle of per-cell `(StarkProof, public_inputs)`
    /// pairs from the same turn.
    ///
    /// Runs the per-proof STARK verifier on each pair (against the standard
    /// `EffectVmAir`) and then calls
    /// [`verify_proof_carrying_turn_bundle`] to enforce that the shared
    /// γ.0a PI slots agree across proofs and (when `turn` is supplied)
    /// against the canonical Turn projection.
    ///
    /// Note: this convenience handles the default-AIR path only; the
    /// custom-program-VK path is the caller's responsibility because the
    /// per-cell AIR identity is cell-dependent in that case. The single-cell
    /// `verify_and_commit_proof` remains the path of record for production
    /// today; this helper exists to back tests and to give future
    /// multi-cell aggregation callers (Stage 7-γ.1+) a stable entry point.
    ///
    /// v1 floor only (takes a v1 `EffectVmAir` `StarkProof` bundle).
    #[cfg(not(feature = "prover"))]
    pub fn verify_bundle_with_stark(
        bundle: &[(
            dregg_circuit::stark::StarkProof,
            Vec<dregg_circuit::field::BabyBear>,
        )],
        turn: Option<&Turn>,
    ) -> Result<(), TurnError> {
        Self::verify_bundle_with_stark_and_ledger(bundle, turn, None)
    }

    /// Snapshot-aware variant of `verify_bundle_with_stark` that threads a
    /// `&Ledger` into the binding-proof sweep. Closes AIR #75 for callers
    /// who carry a Burn binding proof in `turn.effect_binding_proofs`.
    ///
    /// v1 floor only (takes a v1 `EffectVmAir` `StarkProof` bundle).
    #[cfg(not(feature = "prover"))]
    pub fn verify_bundle_with_stark_and_ledger(
        bundle: &[(
            dregg_circuit::stark::StarkProof,
            Vec<dregg_circuit::field::BabyBear>,
        )],
        turn: Option<&Turn>,
        ledger: Option<&Ledger>,
    ) -> Result<(), TurnError> {
        // The v1 hand-AIR (`EffectVmAir`) per-proof STARK verify is RETIRED; a v1
        // `StarkProof` bundle fails closed (rotated bundles verify through the rotated
        // proof-carrying path).
        if !bundle.is_empty() {
            return Err(TurnError::ProofVerificationFailed(
                "v1 hand-AIR StarkProof bundle verify is retired".to_string(),
            ));
        }
        let pi_vecs: Vec<Vec<_>> = bundle.iter().map(|(_, pis)| pis.clone()).collect();
        Self::verify_proof_carrying_turn_bundle_with_ledger(&pi_vecs, turn, ledger)
    }

    /// Read the per-cell `max_custom_effects` from the cell's program manifest.
    ///
    /// Per `DESIGN-max-custom-effects.md` §4. Falls back to
    /// [`dregg_circuit::effect_vm::pi::MAX_CUSTOM_EFFECTS_DEFAULT`] if the cell
    /// has no explicit declaration (hosted or legacy sovereign cells).
    ///
    /// Stage 1: looks at sovereign registration's `max_custom_effects` optional
    /// field (added in this stage). Stage 8 may move the source of truth into
    /// `cell::CellProgram::max_custom_effects` directly.
    ///
    /// V1-only (consumed by `verify_and_commit_proof_v1`'s PI reconstruction);
    /// dead under `prover`, deleted with the v1 leg at C7.
    #[cfg_attr(feature = "prover", allow(dead_code))]
    pub(super) fn read_cell_max_custom_effects(&self, cell_id: &CellId, ledger: &Ledger) -> u8 {
        if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
            if let Some(m) = reg.max_custom_effects {
                return m;
            }
        }
        dregg_circuit::effect_vm::pi::MAX_CUSTOM_EFFECTS_DEFAULT
    }

    /// Read the federation-scoped `approved_handoffs_root` as 4 BabyBear felts.
    ///
    /// Stage 1: returns the empty-tree sentinel (`Commitment4::empty()`).
    /// Stage 7 populates this from federation state when CapTP runtime
    /// emitters land. Per `DESIGN-captp-integration.md` §4.2.
    ///
    /// V1-only (consumed by `verify_and_commit_proof_v1`'s PI reconstruction);
    /// dead under `prover`, deleted with the v1 leg at C7.
    #[cfg_attr(feature = "prover", allow(dead_code))]
    pub(super) fn read_approved_handoffs_root(&self) -> [dregg_circuit::field::BabyBear; 4] {
        [dregg_circuit::field::BabyBear::ZERO; 4]
    }

    /// Get the verification key hash for a sovereign cell, if one is set.
    ///
    /// Checks both the sovereign registration (which has an explicit `verification_key_hash`
    /// field) and the cell's `verification_key` (for hosted cells or legacy sovereign cells).
    pub(crate) fn get_cell_vk_hash(&self, cell_id: &CellId, ledger: &Ledger) -> Option<[u8; 32]> {
        // Check sovereign registration first (proof-carrying path).
        if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
            if let Some(vk_hash) = reg.verification_key_hash {
                return Some(vk_hash);
            }
        }
        // Fallback: check if the cell itself has a verification_key with a hash.
        if let Some(cell) = ledger.get(cell_id) {
            if let Some(vk) = &cell.verification_key {
                return Some(vk.hash);
            }
        }
        None
    }

    /// Convert 4 BabyBear elements to a 16-byte array (for custom proof commitment matching).
    /// V1-only (the rotated verify path reconstructs PIs from the trace generator); dead under
    /// `prover`.
    #[cfg_attr(feature = "prover", allow(dead_code))]
    pub(super) fn babybear4_to_bytes16(elems: &[dregg_circuit::field::BabyBear; 4]) -> [u8; 16] {
        let mut result = [0u8; 16];
        for (i, elem) in elems.iter().enumerate() {
            result[i * 4..i * 4 + 4].copy_from_slice(&elem.0.to_le_bytes());
        }
        result
    }

    /// Convert 8 BabyBear elements to a 32-byte array (PI v2 VK hash key).
    ///
    /// AIR-SOUNDNESS-AUDIT.md #70: the registry now binds against the full
    /// 32-byte VK hash. The pre-v2 path used `babybear4_to_bytes16` plus
    /// `expand_vk_hash_16_to_32` (zero-padded upper 16 bytes), giving 80-bit
    /// effective security in a 128-bit system. The full 32-byte form
    /// distinguishes VK hashes whose lower 16 bytes collide.
    #[cfg_attr(feature = "prover", allow(dead_code))]
    pub(super) fn babybear8_to_bytes32(elems: &[dregg_circuit::field::BabyBear; 8]) -> [u8; 32] {
        let mut result = [0u8; 32];
        for (i, elem) in elems.iter().enumerate() {
            result[i * 4..i * 4 + 4].copy_from_slice(&elem.0.to_le_bytes());
        }
        result
    }

    /// Hash custom proof bytes to produce a 16-byte commitment (matching BabyBear[4]).
    #[cfg_attr(feature = "prover", allow(dead_code))]
    pub(super) fn hash_custom_proof(proof_bytes: &[u8]) -> [u8; 16] {
        let h = blake3::hash(proof_bytes);
        let bytes = h.as_bytes();
        let mut result = [0u8; 16];
        result.copy_from_slice(&bytes[..16]);
        result
    }

    /// **DEPRECATED** — see `babybear8_to_bytes32`.
    ///
    /// Pre-v2 (`pi::VK_PI_LAYOUT_VERSION == 1`) expanded a 16-byte VK hash
    /// (from 4 BabyBear elements) to a 32-byte registry key by zero-padding
    /// the upper 16 bytes. This gave 80-bit effective security: any two
    /// VK hashes that collide on the lower 16 bytes (~2^64 work) dispatch
    /// to the same handler regardless of their upper 16 bytes.
    /// `AIR-SOUNDNESS-AUDIT.md` #70 closed this by widening the PI vk_hash
    /// to 8 felts (full 32 bytes); see `babybear8_to_bytes32`. This helper
    /// is retained only so legacy callers compile; no live dispatch path
    /// uses it.
    #[deprecated(note = "PI layout v3: use babybear8_to_bytes32 against the full 8-felt PI slot")]
    #[allow(dead_code)]
    pub(super) fn expand_vk_hash_16_to_32(short: &[u8; 16]) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[..16].copy_from_slice(short);
        result
    }

    /// Decode a stored [u8; 32] commitment to a single BabyBear field element.
    ///
    /// The stored commitment encodes a Poseidon2 CellState commitment as a
    /// 32-byte BLAKE3-style canonical hash. See the cell crate's
    /// `compute_canonical_state_commitment` for the canonical encoding.
    ///
    /// STAGE 1 (resolves REVIEW[effect-vm-coord], P0-2 in AUDIT-turn-executor.md):
    /// the 4-byte truncation has been replaced with a 4-felt Poseidon2 form
    /// (~124-bit binding) via [`commitment_to_4bb`]. The legacy single-felt
    /// `commitment_to_babybear` retained here for backward-compat with
    /// callers that absorb commitments into Merkle leaves; it now derives
    /// the felt from the full 32-byte canonical commitment rather than a
    /// 4-byte truncation.
    pub fn commitment_to_babybear(bytes: &[u8; 32]) -> dregg_circuit::field::BabyBear {
        // Position 0 of the 4-felt form is the in-trace continuity binding.
        Self::commitment_to_4bb(bytes)[0]
    }

    /// Decode a 32-byte stored commitment into the 4-felt Poseidon2 form used
    /// by the Effect VM AIR's PI[OLD_COMMIT_BASE..+4] / PI[NEW_COMMIT_BASE..+4].
    ///
    /// The stored commitment format (written by [`commitment_4bb_to_bytes`]) packs
    /// 4 BabyBear felts as 4 consecutive LE u32 values in bytes 0..15. The upper
    /// 16 bytes are zero padding. This is the canonical round-trip format that
    /// matches `CellState::compute_commitment_4` — the function the AIR trace
    /// generator uses to populate the commitment PI slots.
    ///
    /// This replaces the former `canonical_32_to_felts_4` call which hashed the
    /// stored bytes (a one-way operation producing different values than
    /// `compute_commitment_4`), causing a byte-incompatible PI mismatch between
    /// trace generation and verification (Silver-Vision bug: sovereign-cell proofs
    /// always rejected, GitHub #99).
    pub fn commitment_to_4bb(bytes: &[u8; 32]) -> [dregg_circuit::field::BabyBear; 4] {
        use dregg_circuit::field::BabyBear;
        [
            BabyBear::new(u32::from_le_bytes(bytes[0..4].try_into().unwrap())),
            BabyBear::new(u32::from_le_bytes(bytes[4..8].try_into().unwrap())),
            BabyBear::new(u32::from_le_bytes(bytes[8..12].try_into().unwrap())),
            BabyBear::new(u32::from_le_bytes(bytes[12..16].try_into().unwrap())),
        ]
    }

    /// Pack 4 BabyBear felts into a 32-byte stored commitment.
    ///
    /// Writes each felt as a LE u32 into bytes 0..15; zeros bytes 16..31.
    /// This is the canonical format read back by [`commitment_to_4bb`].
    /// Use this instead of [`babybear_to_commitment`] when the proof's PI carries
    /// a widened 4-felt commitment (`CellState::compute_commitment_4` output).
    pub fn commitment_4bb_to_bytes(felts: [dregg_circuit::field::BabyBear; 4]) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[0..4].copy_from_slice(&felts[0].0.to_le_bytes());
        result[4..8].copy_from_slice(&felts[1].0.to_le_bytes());
        result[8..12].copy_from_slice(&felts[2].0.to_le_bytes());
        result[12..16].copy_from_slice(&felts[3].0.to_le_bytes());
        result
    }

    /// Encode a single BabyBear field element as a [u8; 32] stored commitment.
    ///
    /// Packs the u32 value into the first 4 bytes (LE), zeroes the rest.
    /// Legacy single-felt encoding; prefer [`commitment_4bb_to_bytes`] for new
    /// proof-carrying paths that use the widened 4-felt PI layout.
    pub fn babybear_to_commitment(bb: dregg_circuit::field::BabyBear) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[..4].copy_from_slice(&bb.0.to_le_bytes());
        result
    }

    /// Compute the AIR-bound 4-felt commitment to a 32-byte Ed25519 owner pubkey
    /// (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.2). Uses `canonical_32_to_felts_4`
    /// so it matches the in-trace witness column. Domain separation from the
    /// state-commitment encoding is provided by the surrounding PI slot
    /// (different position in PI), not by a tag — both inputs are 32 bytes
    /// of opaque commitment material.
    pub fn pubkey_to_witness_key_commit(pubkey: &[u8; 32]) -> [dregg_circuit::field::BabyBear; 4] {
        dregg_commit::typed::canonical_32_to_felts_4(pubkey)
    }

    /// Compute the AIR-bound 4-felt commitment to a transition_proof's
    /// canonical bytes (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.2 / §4.2). The
    /// commitment is `canonical_32_to_felts_4(blake3(proof_bytes))`, picking
    /// up blake3's preimage resistance + the Poseidon2-domain mapping the
    /// AIR uses for everything else.
    pub fn transition_proof_commitment(proof_bytes: &[u8]) -> [dregg_circuit::field::BabyBear; 4] {
        let h = *blake3::hash(proof_bytes).as_bytes();
        dregg_commit::typed::canonical_32_to_felts_4(&h)
    }

    /// Populate the sovereign-witness AIR-teeth PI slots on the verifier
    /// side (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.2).
    ///
    /// `witness` is `Some` when this cell is being verified via the
    /// witness path (the witness object carries the cell's full state
    /// including its public_key). `execution_proof_bytes` is `Some` when
    /// the proof-carrying path is in effect (the bytes ARE the inner
    /// transition proof for Phase 2).
    ///
    /// When neither is supplied, IS_SOVEREIGN_CELL is left as zero (the
    /// hosted-cell path); the boundary constraint holds via sentinel
    /// agreement.
    pub fn populate_sovereign_witness_pi(
        public_inputs: &mut [dregg_circuit::field::BabyBear],
        cell_id: &CellId,
        ledger: &Ledger,
        witness: Option<&crate::turn::SovereignCellWitness>,
        execution_proof_bytes: Option<&[u8]>,
    ) {
        use dregg_circuit::effect_vm::pi;
        use dregg_circuit::field::BabyBear;

        // Default sentinel values (hosted-cell path).
        for i in 0..pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN {
            public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + i] = BabyBear::ZERO;
        }
        public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE] = BabyBear::ZERO;
        public_inputs[pi::IS_SOVEREIGN_CELL] = BabyBear::ZERO;
        for i in 0..pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN {
            public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE + i] = BabyBear::ZERO;
        }
        for i in 0..pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN {
            public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE + i] = BabyBear::ZERO;
        }
        public_inputs[pi::HAS_TRANSITION_PROOF] = BabyBear::ZERO;

        // Phase 1: Bind the witness-identity slots when we have witness
        // material. Source order:
        //   1. Explicit witness object (witness-path turns)
        //   2. Proof-carrying turn (execution_proof_bytes is Some) — bind
        //      IS_SOVEREIGN_CELL=1 + the cell's owning pubkey from
        //      SovereignRegistration::owner_public_key (if populated).
        if let Some(w) = witness {
            // Witness path: the witness carries the cell_state including pubkey.
            let key_commit = Self::pubkey_to_witness_key_commit(w.cell_state.public_key());
            public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE
                ..(pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN)]
                .copy_from_slice(&key_commit[..pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN]);
            public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE] =
                BabyBear::new((w.sequence & 0x7FFF_FFFF) as u32);
            public_inputs[pi::IS_SOVEREIGN_CELL] = BabyBear::ONE;

            // Phase 2: if the witness includes a STARK transition_proof,
            // bind its commitment + VK hash. The VK hash is zero sentinel
            // today (the recursive verifier exposes a stable VK in a
            // follow-up); the off-AIR verifier loop recursively verifies.
            if let Some(proof_bytes) = &w.transition_proof {
                let proof_commit = Self::transition_proof_commitment(proof_bytes);
                public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE
                    ..(pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE
                        + pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN)]
                    .copy_from_slice(
                        &proof_commit[..pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN],
                    );
                public_inputs[pi::HAS_TRANSITION_PROOF] = BabyBear::ONE;
            }
        } else if let Some(_proof_bytes) = execution_proof_bytes {
            // Proof-carrying path: the execution_proof IS the transition proof.
            // Owner pubkey is sourced from the sovereign registration if
            // available, else left as sentinel zero (Phase 1.5: registration
            // grows an owner_public_key field; for now we accept either
            // form and the cclerk matches what the federation knows).
            if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
                if let Some(pk) = reg.owner_public_key {
                    let key_commit = Self::pubkey_to_witness_key_commit(&pk);
                    public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE
                        ..(pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE
                            + pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN)]
                        .copy_from_slice(&key_commit[..pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN]);
                }
            }
            public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE] = BabyBear::new(
                (ledger.last_sovereign_witness_sequence(cell_id) & 0x7FFF_FFFF) as u32,
            );
            public_inputs[pi::IS_SOVEREIGN_CELL] = BabyBear::ONE;
        }
    }

    /// Encode two BabyBear elements as a [u8; 32] for error reporting.
    #[cfg_attr(feature = "prover", allow(dead_code))]
    pub(super) fn babybear_pair_to_bytes32(
        lo: dregg_circuit::field::BabyBear,
        hi: dregg_circuit::field::BabyBear,
    ) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[..4].copy_from_slice(&lo.0.to_le_bytes());
        result[4..8].copy_from_slice(&hi.0.to_le_bytes());
        result
    }

    /// Stage 7-γ.0c: compute the four shared "turn-identity" PI values that
    /// every per-cell proof of `turn` must agree on.
    ///
    /// Returns `(turn_hash[4], effects_hash_global[4], actor_nonce,
    /// previous_receipt_hash[4])` where:
    ///
    /// - `turn_hash` is `canonical_32_to_felts_4(Turn::hash())` (v3, post-α.1).
    /// - `effects_hash_global` is a Poseidon2 absorption chain over the
    ///   canonical-DFS-order traversal of *every* Effect in the call_forest
    ///   (not per-cell). Order: pre-order DFS, root-list order at the top,
    ///   children-list order at each node, action.effects-list order at each
    ///   action. Each Effect contributes its `Effect::hash()` -> 4 felts via
    ///   `canonical_32_to_felts_4`, absorbed into the running 4-felt
    ///   accumulator by element-wise composition with `hash_4_to_1`. The
    ///   empty-forest sentinel is `[BabyBear::ZERO; 4]`.
    /// - `actor_nonce` is `turn.nonce` (closes #49 differential-test gap).
    /// - `previous_receipt_hash` is `canonical_32_to_felts_4` of
    ///   `turn.previous_receipt_hash`, or `[ZERO; 4]` when None.
    ///
    /// The canonical DFS order is the same one a Stage 7-γ.1 aggregation
    /// micro-AIR will replay when checking
    /// `Poseidon2-merge(effects_local[c1..]) == effects_hash_global`, so
    /// any future cross-cell aggregator must match this traversal exactly.
    pub fn compute_turn_identity_pi(
        turn: &Turn,
    ) -> (
        [dregg_circuit::field::BabyBear; 4],
        [dregg_circuit::field::BabyBear; 4],
        u64,
        [dregg_circuit::field::BabyBear; 4],
    ) {
        use dregg_circuit::field::BabyBear;
        use dregg_circuit::poseidon2::hash_4_to_1;
        use dregg_commit::typed::canonical_32_to_felts_4;

        let turn_hash = if turn.execution_proof.is_some() {
            // A proof cannot commit to a hash that includes its own bytes.
            // The AIR-bound identity for proof-carrying turns is therefore
            // the stable pre-proof form: all fields remain bound except the
            // execution_proof bytes, which are verified directly by this path.
            let mut proofless = turn.clone();
            proofless.execution_proof = None;
            proofless.hash()
        } else {
            turn.hash()
        };
        let turn_hash_4 = canonical_32_to_felts_4(&turn_hash);

        // Canonical-DFS-order collection of the WHOLE call_forest's effects.
        // The order must match what a future cross-cell aggregator (γ.1)
        // computes; document it here in one place and keep this helper as
        // the source of truth.
        fn dfs_collect(tree: &CallTree, out: &mut Vec<[u8; 32]>) {
            for effect in &tree.action.effects {
                out.push(effect.hash());
            }
            for child in &tree.children {
                dfs_collect(child, out);
            }
        }
        let mut effect_hashes: Vec<[u8; 32]> = Vec::new();
        for root in &turn.call_forest.roots {
            dfs_collect(root, &mut effect_hashes);
        }

        // Absorb each 32-byte effect hash into a running 4-felt accumulator.
        // The empty-forest case yields the zero sentinel. The absorption rule
        // for one block is acc' = elementwise hash_4_to_1 of [acc[i], blk[i]
        // mixed with index salts]. We use a simple feistel-flavoured pattern:
        //   for each i in 0..4:
        //     acc[i] = hash_4_to_1(&[acc[i], blk[i], acc[(i+1)%4], blk[(i+1)%4]])
        // — distinct salts per position via the rotation, so the four output
        // limbs depend on all eight input limbs. Deterministic and trivially
        // re-implementable in a future aggregation AIR.
        let mut acc: [BabyBear; 4] = [BabyBear::ZERO; 4];
        for h in &effect_hashes {
            let blk = canonical_32_to_felts_4(h);
            let mut next = [BabyBear::ZERO; 4];
            for i in 0..4 {
                let j = (i + 1) % 4;
                next[i] = hash_4_to_1(&[acc[i], blk[i], acc[j], blk[j]]);
            }
            acc = next;
        }
        let effects_hash_global_4 = acc;

        let previous_receipt_hash_4 = match &turn.previous_receipt_hash {
            Some(h) => canonical_32_to_felts_4(h),
            None => [BabyBear::ZERO; 4],
        };

        (
            turn_hash_4,
            effects_hash_global_4,
            turn.nonce,
            previous_receipt_hash_4,
        )
    }

    /// Compute the balance delta (magnitude, sign) from the turn's effects for a cell.
    ///
    /// Returns (magnitude_u32, sign_u32) where sign=0 means positive/incoming,
    /// sign=1 means negative/outgoing.
    /// V1-only (the rotated verify reconstructs balance PIs from the trace generator);
    /// dead under `prover`, deleted with the v1 leg at C7.
    #[cfg_attr(feature = "prover", allow(dead_code))]
    pub(super) fn compute_balance_delta_from_effects(cell_id: &CellId, turn: &Turn) -> (u32, u32) {
        fn walk_delta(tree: &CallTree, cell_id: &CellId, net: &mut i64) {
            for effect in &tree.action.effects {
                match effect {
                    Effect::Transfer { from, to, amount } => {
                        if from == cell_id {
                            *net -= *amount as i64;
                        }
                        if to == cell_id {
                            *net += *amount as i64;
                        }
                    }
                    Effect::NoteSpend { value, .. } => {
                        *net += *value as i64;
                    }
                    Effect::NoteCreate { value, .. } => {
                        *net -= *value as i64;
                    }
                    // Stage 3 honest projections: AIR enforces balance changes
                    // for these variants, so they must contribute to net_delta
                    // for the PI-to-trace consistency constraint to hold.
                    Effect::BridgeMint { portable_proof } => {
                        // BridgeMint credits the actor's balance with the
                        // portable proof's declared value.
                        *net += portable_proof.value as i64;
                    }
                    _ => {}
                }
            }
            for child in &tree.children {
                walk_delta(child, cell_id, net);
            }
        }

        let mut net_delta: i64 = 0;
        for root in &turn.call_forest.roots {
            walk_delta(root, cell_id, &mut net_delta);
        }

        if net_delta < 0 {
            ((-net_delta) as u32, 1u32)
        } else {
            (net_delta as u32, 0u32)
        }
    }
}
