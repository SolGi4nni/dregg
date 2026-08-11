//! Cutover C1 validation — the ROTATED sovereign proof-carrying matched pair.
//!
//! This integration test drives the cutover's first coherent checkpoint
//! (ROTATION-CUTOVER §EXEC, C1): the sovereign producer
//! ([`AgentCipherclerk::execute_sovereign_turn_with_proof`]) now mints a rotated
//! R=24 `Ir2BatchProof` over the cohort descriptor (instead of the weak hand-AIR
//! `EffectVmAir`), carrying the v9 felt commitment; the matched verifier
//! (`dregg_turn`'s `executor::verify_and_commit_proof`, which graduates to
//! `descriptor_ir2::verify_vm_descriptor2`) reconstructs the 38-PI layout from
//! the after-state it holds and accepts.
//!
//! It lives in `sdk/tests/` (a self-contained compilation unit) rather than the
//! workspace `dregg-tests` harness so the C1 matched pair is validatable
//! independently. Requires the `recursion` feature (the SDK default), which
//! compiles the rotated producer + pulls `dregg-circuit/recursion` (the rotated
//! verifier). Under `not(recursion)` the rotated path does not exist, so the
//! test self-skips.

use dregg_cell::{Cell, CellId, CellMode, Ledger};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::{ComputronCosts, Effect, TurnExecutor, TurnResult};

/// Register a sovereign cell with the v9 commitment the rotated producer derives
/// for its before-state (single-cell `cells_root`, empty nullifier root, empty
/// receipt-chain `iroot`). The executor reads this back as OLD_COMMIT (PI 34).
fn setup_sovereign_cell(balance: u64) -> (AgentCipherclerk, CellId, Ledger) {
    let cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(b"c1-domain").as_bytes();

    let mut cell = Cell::with_balance(pub_key, token_id, i64::try_from(balance).unwrap());
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();

    // ⚑ THE SHARED BINDING, not a context rebuilt here. `sovereign_registration_commitment` is the
    // producer's OWN `SovereignTurnCtx::for_cell(..).commitment_8(..)` — a single-cell `cells_root`,
    // the three LIVE empty accumulator roots, the empty-receipt-chain `iroot` — and it takes no root
    // argument, so this fixture cannot name one. It used to name three, all of them
    // `heap_root::empty_heap_root_8()`, which stopped being any live accumulator's empty root at
    // `b20a2c50a`.
    let commitment = dregg_turn::rotation_witness::sovereign_registration_commitment(&cell, &[]);

    let mut cclerk = cclerk;
    cclerk.store_sovereign_state(cell.clone());

    let mut ledger = Ledger::new();
    ledger.register_sovereign_cell(cell_id, commitment).unwrap();
    let _ = ledger.insert_cell(cell);

    (cclerk, cell_id, ledger)
}

/// CONTROL: an honest rotated sovereign turn proves (rotated `Ir2BatchProof`) and
/// the executor ACCEPTS it through the rotated `verify_vm_descriptor2` leg, then
/// advances the stored v9 commitment.
#[test]
fn rotated_sovereign_turn_proves_and_verifies() {
    let (mut cclerk, cell_id, mut ledger) = setup_sovereign_cell(1000);

    let dest_cell = Cell::with_balance([42u8; 32], *blake3::hash(b"c1-domain").as_bytes(), 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 100,
    }];

    let turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 500, 0)
        .expect("rotated sovereign turn should prove");

    // The proof is real, postcard-encoded (NOT the `DREG`-magic hand-AIR wire).
    let proof_bytes = turn
        .execution_proof
        .as_ref()
        .expect("execution_proof attached");
    assert!(!proof_bytes.is_empty());
    assert_ne!(
        &proof_bytes[0..4],
        b"DREG",
        "rotated wire is a postcard BatchProof"
    );
    assert_eq!(turn.execution_proof_cell, Some(cell_id));
    assert!(turn.execution_proof_new_commitment.is_some());
    assert!(turn.sovereign_witnesses.is_empty());

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        other => panic!("rotated sovereign turn must commit, got {other:?}"),
    }

    // The stored sovereign commitment advanced to the proven post-state (v9 felt).
    let new_commitment = ledger
        .get_sovereign_commitment(&cell_id)
        .expect("commitment present after commit");
    assert_eq!(
        *new_commitment,
        turn.execution_proof_new_commitment.unwrap()
    );
}

/// ANTI-GHOST: a rotated sovereign turn whose claimed post-state commitment is
/// FORGED is REJECTED — the forged PI 35 disagrees with the trace's after-block
/// `STATE_COMMIT` carrier (the descriptor's col-261 `pi_binding`), so
/// `verify_vm_descriptor2` fails.
#[test]
fn rotated_sovereign_forged_post_state_is_rejected() {
    let (mut cclerk, cell_id, mut ledger) = setup_sovereign_cell(1000);

    let dest_cell = Cell::with_balance([43u8; 32], *blake3::hash(b"c1-domain").as_bytes(), 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 50,
    }];

    let mut turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 500, 0)
        .expect("rotated sovereign turn should prove");

    // Forge the claimed post-state commitment.
    turn.execution_proof_new_commitment = Some([0xFFu8; 32]);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("ProofVerificationFailed") || s.contains("rotated"),
                "expected a rotated verify rejection, got: {s}"
            );
        }
        other => panic!("ANTI-GHOST: forged post-state must be rejected, got {other:?}"),
    }
}

// ===========================================================================
// THE RECORD-PIN ANCHOR — setPermissions BEACHHEAD (deployment-soundness close).
//
// The rotated record-pin descriptor (`setPermsVmDescriptor2R24`, 39 PIs) welds the AFTER
// block's `B_RECORD_DIGEST` limb (col 256) to rotated PI 38. PI 38 is a FREE public input the
// prover fills from its honest after-cell's authority digest — so the pin alone is a
// published-value binding, NOT a forcing gate, UNTIL the verifier independently ANCHORS PI 38 to
// `compute_authority_digest_felt(trusted before-cell + effect)` through the SHARED
// `apply_effect_to_cell` weld (`verify_and_commit_proof_rotated`'s record-pin anchor). These two
// tests close that gate:
//   * `rotated_sovereign_set_permissions_proves_and_verifies` — an HONEST setPermissions turn
//     proves → verifies → ACCEPT, and the committed cell's permissions changed. This itself BITES:
//     without the anchor the verifier leaves PI 38 at the placeholder reconstruction (0), which
//     disagrees with the honest proof's nonzero after-digest ⇒ the honest turn would be REJECTED.
//   * `rotated_sovereign_forged_after_permissions_is_rejected` — a proof whose after-block
//     record-digest is for permissions the effect did NOT produce (the kernel effect sets
//     `zkapp()`, the proof's after-block carries `frozen()`), with all OTHER PIs honest, is
//     REJECTED: the anchored PI 38 = digest(zkapp) ≠ the proof's bound col-256 = digest(frozen)
//     ⇒ `verify_vm_descriptor2` UNSAT.
// ===========================================================================
mod record_pin_anchor {
    use dregg_cell::{Cell, CellMode, Ledger, Permissions};
    use dregg_sdk::AgentCipherclerk;
    use dregg_turn::rotation_witness as rw;
    use dregg_turn::{ComputronCosts, Effect, Turn, TurnExecutor, TurnResult};

    /// Re-derive the same sovereign-cell registration `setup_sovereign_cell` produces, but expose
    /// the before-`Cell` so the forged test can build witnesses over it. Returns the live
    /// cipherclerk + cell + ledger + the before-cell clone.
    fn setup_with_cell(balance: u64) -> (AgentCipherclerk, dregg_cell::CellId, Ledger, Cell) {
        let cclerk = AgentCipherclerk::new();
        let pub_key = cclerk.public_key().0;
        let token_id = *blake3::hash(b"c1-domain").as_bytes();

        let mut cell = Cell::with_balance(pub_key, token_id, i64::try_from(balance).unwrap());
        cell.mode = CellMode::Sovereign;
        let cell_id = cell.id();

        // THE SHARED BINDING — the producer's own context builder, and no root is named here.
        // `sovereign_registration_commitment` takes (cell, receipt log) and nothing else.
        let commitment = rw::sovereign_registration_commitment(&cell, &[]);

        let mut cclerk = cclerk;
        cclerk.store_sovereign_state(cell.clone());

        let mut ledger = Ledger::new();
        ledger.register_sovereign_cell(cell_id, commitment).unwrap();
        let _ = ledger.insert_cell(cell.clone());

        (cclerk, cell_id, ledger, cell)
    }

    /// CONTROL + BITE: an HONEST sovereign `SetPermissions` turn proves and verifies, the committed
    /// permissions changed. This passes ONLY because the verifier anchors PI 38 to the trusted
    /// post-cell digest; without the anchor the placeholder PI 38 (0) would reject this honest turn.
    #[test]
    fn rotated_sovereign_set_permissions_proves_and_verifies() {
        let (mut cclerk, cell_id, mut ledger, _before) = setup_with_cell(1000);

        // The before-cell carries the default permissions; the turn locks it down to `zkapp()`.
        let new_perms = Permissions::zkapp();
        assert_ne!(
            new_perms,
            Permissions::default(),
            "the test must actually change permissions"
        );

        let effects = vec![Effect::SetPermissions {
            cell: cell_id,
            new_permissions: new_perms.clone(),
        }];

        let turn = cclerk
            .execute_sovereign_turn_with_proof(&cell_id, effects, 0, 0)
            .expect("rotated sovereign setPermissions turn should prove");

        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            // The proof VERIFYING (not rejected) is the proof the anchor accepted: the verifier's
            // anchored PI 38 = digest(before + zkapp) EQUALS the proof's bound after-limb. Without
            // the anchor the verifier would carry PI 38 = placeholder 0 ≠ the honest after-digest
            // and reject — so a Committed result here exercises the anchor's accept side.
            TurnResult::Committed { .. } => {}
            other => panic!("honest setPermissions turn must commit, got {other:?}"),
        }

        // The federation sovereign commitment advanced to the proven post-state (the proof path is
        // commitment-only at the federation; the cell's full state lives with the cipherclerk).
        let committed_commitment = ledger
            .get_sovereign_commitment(&cell_id)
            .expect("sovereign commitment present after commit");
        assert_eq!(
            *committed_commitment,
            turn.execution_proof_new_commitment.unwrap(),
            "the sovereign commitment must advance to the proven post-state"
        );

        // The cipherclerk's LOCAL sovereign state carries the new permissions — the producer
        // applied the effect through the SHARED `apply_effect_to_cell` weld, the SAME projection the
        // verifier anchored PI 38 against (the anti-drift guarantee: both sides moved together).
        let local = cclerk
            .sovereign_state(&cell_id)
            .expect("cipherclerk local sovereign state present");
        assert_eq!(
            local.permissions, new_perms,
            "the cipherclerk's after-state permissions must be the turn's new value"
        );
    }

    /// ANTI-GHOST (the setPermissions record-digest anchor BITES): a proof whose AFTER block carries
    /// `frozen()` permissions — which the `zkapp()` effect did NOT produce — is REJECTED. Every OTHER
    /// PI is honest (the kernel effect sets `zkapp()`, so the verifier's reconstructed `vm_effects` /
    /// `effects_hash` MATCH the proof) and so is the universal-memory leg, so the refusal is ISOLATED
    /// to the authority residue this member forces: anchored digest(zkapp) ≠ the proof's bound
    /// col-256 digest(frozen).
    ///
    /// ⚑ This was a hand-rolled twin of the shared driver riding the BARE rotated prover and
    /// publishing a 1-felt `execution_proof_new_commitment`. It stayed GREEN only because its forgery
    /// is refused at PROVE time and it therefore never reached the executor at all — i.e. it had NO
    /// honest pole, the same shape that let five sibling forge tests read one routing refusal as five
    /// different anchors. It rides the shared driver now, honest pole included.
    #[test]
    fn rotated_sovereign_forged_after_permissions_is_rejected() {
        let (_c, cell_id, ledger, before_cell) = setup_with_cell(1000);

        let honest_perms = Permissions::zkapp();
        let forged_perms = Permissions::frozen();
        assert_ne!(
            honest_perms, forged_perms,
            "the plant must actually move the permissions"
        );

        let effects = vec![Effect::SetPermissions {
            cell: cell_id,
            new_permissions: honest_perms,
        }];
        // BOTH post-states go through the SHARED `apply_effect_to_cell` weld, so the ONLY difference
        // between them is the permissions value the forgery claims — the plant is localized by
        // construction, not by hoping the hand-built twin matched.
        let mut honest_after = before_cell.clone();
        rw::apply_effect_to_cell(&mut honest_after, &cell_id, &effects[0], 0);
        let mut forged_after = before_cell.clone();
        rw::apply_effect_to_cell(
            &mut forged_after,
            &cell_id,
            &Effect::SetPermissions {
                cell: cell_id,
                new_permissions: forged_perms,
            },
            0,
        );

        assert_forged_after_rejected(
            cell_id,
            &before_cell,
            &effects,
            &honest_after,
            &forged_after,
            AnchorMember::SET_PERMISSIONS,
            ledger,
            0,
            "setPermissions forged-after (frozen, not zkapp)",
        );
    }

    /// CONTROL + BITE (setVK fan-out): an HONEST sovereign `SetVerificationKey` turn proves and
    /// verifies. setVK is the record-digest sibling of setPermissions — `compute_authority_digest_felt`
    /// folds `vk.hash`, so the after r23 residue MOVES, and the verifier anchor's accept side is
    /// exercised (without the anchor the placeholder PI 38 = 0 would reject this honest turn).
    #[test]
    fn rotated_sovereign_set_vk_proves_and_verifies() {
        let (mut cclerk, cell_id, mut ledger, before) = setup_with_cell(1000);
        assert!(before.verification_key.is_none(), "before cell has no VK");

        // A canonical VK whose declared hash == blake3(data) (the executor's apply integrity gate).
        #[allow(deprecated)]
        let vk = dregg_cell::VerificationKey::new(b"c1-setvk-program".to_vec());
        let effects = vec![Effect::SetVerificationKey {
            cell: cell_id,
            new_vk: Some(vk.clone()),
        }];

        let turn = cclerk
            .execute_sovereign_turn_with_proof(&cell_id, effects, 0, 0)
            .expect("rotated sovereign setVK turn should prove");

        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!("honest setVK turn must commit, got {other:?}"),
        }

        // The cipherclerk's LOCAL sovereign state carries the installed VK (the producer applied the
        // effect through the SHARED `apply_effect_to_cell` weld — the SAME projection the verifier
        // anchored PI 38 against).
        let local = cclerk
            .sovereign_state(&cell_id)
            .expect("cipherclerk local sovereign state present");
        assert_eq!(
            local.verification_key.as_ref().map(|v| v.hash),
            Some(vk.hash),
            "the cipherclerk's after-state VK must be the turn's new value"
        );
    }

    /// ANTI-GHOST (the setVK record-digest anchor BITES): a proof whose AFTER block installs a
    /// DIFFERENT VK than the kernel effect does is REJECTED. Every other PI is honest (the kernel
    /// effect installs `vk_honest`, so the reconstructed vm-effects / effects_hash MATCH) and so is
    /// the universal-memory leg, so the refusal is ISOLATED to the authority residue: anchored
    /// digest(vk_honest) ≠ the proof's bound col-256 digest(vk_forged).
    ///
    /// ⚑ Same repair as its setPermissions sibling: it was a hand-rolled twin on the BARE prover with
    /// a 1-felt commitment claim and no honest pole, green only because it never reached the executor.
    #[test]
    fn rotated_sovereign_forged_after_vk_is_rejected() {
        let (_c, cell_id, ledger, before_cell) = setup_with_cell(1000);
        assert!(before_cell.verification_key.is_none(), "before cell has no VK");

        #[allow(deprecated)]
        let vk_honest = dregg_cell::VerificationKey::new(b"c1-setvk-honest".to_vec());
        #[allow(deprecated)]
        let vk_forged = dregg_cell::VerificationKey::new(b"c1-setvk-FORGED".to_vec());

        let effects = vec![Effect::SetVerificationKey {
            cell: cell_id,
            new_vk: Some(vk_honest),
        }];
        // BOTH post-states through the SHARED weld — only the installed VK differs.
        let mut honest_after = before_cell.clone();
        rw::apply_effect_to_cell(&mut honest_after, &cell_id, &effects[0], 0);
        let mut forged_after = before_cell.clone();
        rw::apply_effect_to_cell(
            &mut forged_after,
            &cell_id,
            &Effect::SetVerificationKey {
                cell: cell_id,
                new_vk: Some(vk_forged),
            },
            0,
        );

        assert_forged_after_rejected(
            cell_id,
            &before_cell,
            &effects,
            &honest_after,
            &forged_after,
            AnchorMember::SET_VK,
            ledger,
            0,
            "setVK forged-after (a VK the effect did not install)",
        );
    }

    // ───────────────────────────────────────────────────────────────────────────────────────────
    // THE RECORD-PIN FAN-OUT CLOSE (#218/#219/#220): the lifecycle family (cellSeal/cellUnseal/
    // cellDestroy → limb 29 via `lifecycle_felt_cell`; receiptArchive → limb 29, re-routed from
    // the prior record-digest MIS-ROUTE) and the refusal record-digest pin (limb 24 via
    // `compute_authority_digest_felt`, the deployed `apply_refusal` now writing the audit into
    // `fields_root`). Each effect gets an HONEST accept (the producer + verifier route the effect
    // through the SHARED `apply_effect_to_cell` so the after-limb the prover binds EQUALS the
    // verifier's independently-recomputed anchor) and a FORGED-after reject (a proof whose after-
    // limb is for a post-state the effect did NOT produce, every other PI honest, REJECTED by the
    // anchor mismatch). The accept side BITES: without the anchor the verifier leaves PI 38 at the
    // placeholder reconstruction (0), which disagrees with the honest after-limb ⇒ the honest turn
    // is REJECTED (the same disable-the-anchor argument the setPermissions/setVK pairs make).
    // ───────────────────────────────────────────────────────────────────────────────────────────

    /// Same as `setup_with_cell`, but applies `mutate` to the cell BEFORE registration/storage so
    /// the cipherclerk's local before-state (and the federation registration commitment) reflect a
    /// non-default lifecycle (e.g. a pre-Sealed cell for the cellUnseal accept test).
    fn setup_with_mutated_cell(
        balance: u64,
        mutate: impl FnOnce(&mut Cell),
    ) -> (AgentCipherclerk, dregg_cell::CellId, Ledger, Cell) {
        let cclerk = AgentCipherclerk::new();
        let pub_key = cclerk.public_key().0;
        let token_id = *blake3::hash(b"c1-domain").as_bytes();

        let mut cell = Cell::with_balance(pub_key, token_id, i64::try_from(balance).unwrap());
        cell.mode = CellMode::Sovereign;
        mutate(&mut cell);
        let cell_id = cell.id();

        // THE SHARED BINDING — the producer's own context builder, and no root is named here.
        // `sovereign_registration_commitment` takes (cell, receipt log) and nothing else.
        let commitment = rw::sovereign_registration_commitment(&cell, &[]);

        let mut cclerk = cclerk;
        cclerk.store_sovereign_state(cell.clone());

        let mut ledger = Ledger::new();
        ledger.register_sovereign_cell(cell_id, commitment).unwrap();
        let _ = ledger.insert_cell(cell.clone());

        (cclerk, cell_id, ledger, cell)
    }

    /// A canonical death certificate for `cell_id` (the cellDestroy reflected-cert tests).
    fn death_cert(cell_id: dregg_cell::CellId) -> dregg_cell::lifecycle::DeathCertificate {
        dregg_cell::lifecycle::DeathCertificate {
            cell_id,
            last_receipt_hash: [4u8; 32],
            final_state_commitment: [5u8; 32],
            destroyed_at_height: 9,
            reason: dregg_cell::lifecycle::DeathReason::Voluntary,
        }
    }

    /// A canonical archival attestation for `cell_id` (the receiptArchive tests).
    fn archive_att(cell_id: dregg_cell::CellId) -> dregg_cell::lifecycle::ArchivalAttestation {
        dregg_cell::lifecycle::ArchivalAttestation {
            cell_id,
            archive_start_height: 0,
            archive_end_height: 5,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        }
    }

    /// Which forced-limb anchor a record-pin effect uses (chooses the verifier's felt recompute).
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    enum AnchorFlavor {
        /// `compute_authority_digest_felt` (limb 24 — refusal / makeSovereign in this fan-out).
        RecordDigest,
        /// `lifecycle_felt_cell` (limb 29 — the lifecycle family + receiptArchive).
        Lifecycle,
    }

    impl AnchorFlavor {
        fn felt(self, cell: &Cell) -> dregg_circuit::field::BabyBear {
            match self {
                AnchorFlavor::RecordDigest => dregg_cell::compute_authority_digest_felt(cell),
                AnchorFlavor::Lifecycle => rw::lifecycle_felt_cell(cell),
            }
        }

        /// The OTHER forced limb — the one a plant aimed at `self` must leave ALONE.
        ///
        /// The two flavors are the verifier's two independent recomputes
        /// (`verify_one_cohort_run`'s `Anchor::RecordDigest` / `Anchor::Lifecycle` arms), and a
        /// plant that moves BOTH cannot say which one refused it. Asserting the sibling limb is
        /// UNMOVED is what makes "this forgery fails for the anchor it names" a measurement rather
        /// than a label.
        fn sibling(self) -> AnchorFlavor {
            match self {
                AnchorFlavor::RecordDigest => AnchorFlavor::Lifecycle,
                AnchorFlavor::Lifecycle => AnchorFlavor::RecordDigest,
            }
        }
    }

    /// **THE DEPLOYED MEMBER A FORGE TEST NAMES — RESOLVED BY REGISTRY KEY, NEVER BY DISPLAY NAME.**
    ///
    /// Display names COLLIDE in this registry (`attenuateVmDescriptor2R24` and
    /// `revokeCapabilityVmDescriptor2R24` are both `dregg-effectvm-attenuateA-v1-genuine-…` at 559
    /// against 558 constraints), so a member is identified by its key and the wire name is DERIVED
    /// from the key through the Lean-emitted weld table. That derived wire name is exactly the
    /// string `verify_one_cohort_run` puts in its refusal (`format!("{}: {e}", d.name)`), which is
    /// how each of these six tests can assert it was refused by ITS OWN member rather than by
    /// whatever shared thing happened to fire first.
    #[derive(Clone, Copy)]
    struct AnchorMember {
        /// The WIDE registry key `rotated_descriptor_name_for_effect` must resolve for this lead.
        key: &'static str,
        /// The forced limb the verifier's record-pin anchor recomputes for this member.
        flavor: AnchorFlavor,
    }

    impl AnchorMember {
        const CELL_SEAL: AnchorMember = AnchorMember {
            key: "cellSealVmDescriptor2R24",
            flavor: AnchorFlavor::Lifecycle,
        };
        const CELL_UNSEAL: AnchorMember = AnchorMember {
            key: "cellUnsealVmDescriptor2R24",
            flavor: AnchorFlavor::Lifecycle,
        };
        const CELL_DESTROY: AnchorMember = AnchorMember {
            key: "cellDestroyVmDescriptor2R24",
            flavor: AnchorFlavor::Lifecycle,
        };
        const RECEIPT_ARCHIVE: AnchorMember = AnchorMember {
            key: "receiptArchiveVmDescriptor2R24",
            flavor: AnchorFlavor::Lifecycle,
        };
        const REFUSAL: AnchorMember = AnchorMember {
            key: "refusalVmDescriptor2R24",
            flavor: AnchorFlavor::RecordDigest,
        };
        const MAKE_SOVEREIGN: AnchorMember = AnchorMember {
            key: "makeSovereignVmDescriptor2R24",
            flavor: AnchorFlavor::RecordDigest,
        };
        const SET_PERMISSIONS: AnchorMember = AnchorMember {
            key: "setPermsVmDescriptor2R24",
            flavor: AnchorFlavor::RecordDigest,
        };
        const SET_VK: AnchorMember = AnchorMember {
            key: "setVKVmDescriptor2R24",
            flavor: AnchorFlavor::RecordDigest,
        };

        /// The WELDED twin's wire name for this key, read out of the Lean-emitted weld table
        /// (`UMEM_WELD_TABLE`). This is the member the deployed executor REQUIRES
        /// (`verify_one_cohort_run`'s `require_welded` drops the bare wide twin), so it is also the
        /// member whose name appears in the refusal when the anchor bites at verify time.
        fn welded_wire_name(self) -> &'static str {
            dregg_circuit::effect_vm_descriptors::umem_weld_row(self.key)
                .unwrap_or_else(|| {
                    panic!(
                        "{}: no Lean-emitted welded twin — the deployed executor requires one for \
                         this key, so a forge test pointed here could never reach its anchor",
                        self.key
                    )
                })
                .name
        }

        /// The producer's OWN descriptor resolution for `lead` lands on this member's key.
        ///
        /// This is the routing half of "the test reaches the anchor it names": if the lead resolved
        /// somewhere else, every verdict below would be about a different member's gate.
        fn assert_routes(self, lead: &dregg_circuit::effect_vm::Effect, what: &str) {
            let resolved =
                dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect(lead)
                    .unwrap_or_else(|| {
                        panic!("{what}: the lead effect {lead:?} resolves NO wide descriptor")
                    });
            assert_eq!(
                resolved, self.key,
                "{what}: this test names the {} member, but the deployed producer routes its lead \
                 to {resolved} — the forgery below would be measuring another member's gate",
                self.key
            );
        }
    }

    /// **THE LEG THE DEPLOYED PRODUCER MINTS.** `prove_wide_umem_welded_staged` — the WIDE
    /// (8-felt / ~124-bit) rotated cohort descriptor with the universal-memory reconciliation leg
    /// welded on — is what `cipherclerk::prove_sovereign_turn_rotated` calls for a weldable
    /// single-cohort sovereign turn, and `umem_weld_staged_enabled` is `true` in every constructor.
    /// The deployed executor then DROPS the bare wide member from its accept set
    /// (`verify_one_cohort_run`'s `require_welded`, the G4 flip), so a bare leg is refused on
    /// ROUTING — before any record-pin anchor is consulted.
    ///
    /// ⚑ **THAT IS WHY THIS FUNCTION EXISTS.** Until `2fd097812` this module minted with
    /// `prove_effect_vm_rotated_ir2_with_caveat` (the BARE rotated prover), so five forge tests named
    /// for five different anchors were all reading one routing refusal — *"proof bound NO descriptor
    /// (welded twin present, bare wide DROPPED (welded required — G4 flip))"* — through a
    /// `Rejected` arm that accepted any reason containing `ProofVerificationFailed`.
    ///
    /// ⚠ **The count is five, not six, and the correction matters.** `2fd097812`'s tooth docblock
    /// attributed all six shared-driver reds to the routing refusal. Measured at that commit: five
    /// were (cellSeal / cellUnseal / cellDestroy / receiptArchive / makeSovereign), and the sixth —
    /// `refusal` — died one layer earlier and for its own reason, *"map op 0: no witness heap with
    /// root8 …"*: the driver never threaded the `.write`-gate `refusal_fields` context the deployed
    /// producer builds, so its honest pole was unprovable rather than misrouted. Naming a shared
    /// cause is exactly the move that hid this class in the first place, so it is worth being
    /// literal: three distinct causes stacked here, not one.
    ///
    /// ⚑ **AND THE ROUTING WAS NOT THE ONLY SHARED CAUSE.** This module also published
    /// `felt_to_bytes32(commitment_felt(after))` as `execution_proof_new_commitment` — the 1-felt
    /// `wireCommitR` in bytes `0..4` with 28 zero bytes after it — while `Ledger::register_sovereign_cell`
    /// stores `SovereignTurnCtx::commitment_8` (the FAITHFUL 8-felt) and the executor reads the claim
    /// back through `bytes32_to_felt8` to anchor the proof's 16 wide commit PIs. Every leg minted here
    /// therefore disagreed with the verifier on the AFTER anchors regardless of what it proved. Both
    /// poles now publish the proof's OWN wide PI tail, which is the deployed producer's derivation.
    ///
    /// `bound_after` is the after-BLOCK this leg binds — the honest post-state on the honest pole,
    /// the forgery on the other. `umem_after` is the post-state the universal-memory cohort leg
    /// reconciles, and it is the HONEST one on BOTH poles, deliberately:
    ///
    ///   * the weld is purely additive (`weld_umem_into_wide_descriptor` appends 7 columns and ONE
    ///     constraint PAST the wide carriers, touching no PI binding), so the umem leg publishes
    ///     nothing the record-pin anchor reads — handing the forger a well-formed one is the
    ///     adversary-FAVOURABLE choice, and the anchor still has to bite;
    ///   * three of the eight plants (a frozen seal, a frozen archive, an un-promoted makeSovereign)
    ///     are *"the after-state did not move"*, so their own record-kernel diff is EMPTY. Projecting
    ///     the umem leg from the forgery would refuse them on the empty cohort — one shared refusal
    ///     again, wearing a different mask.
    fn mint_welded_leg(
        cell_id: dregg_cell::CellId,
        before_cell: &Cell,
        effects: &[Effect],
        bound_after: &Cell,
        umem_after: &Cell,
    ) -> Result<(Vec<u8>, [u8; 32], Vec<dregg_circuit::field::BabyBear>), dregg_sdk::SdkError> {
        use dregg_circuit::field::BabyBear;
        use dregg_sdk::full_turn_proof::prove_wide_umem_welded_staged;
        use dregg_turn::umem::{project_diff_ops, project_record_kernel_state};

        let vm_effects = AgentCipherclerk::convert_effects_to_vm(&cell_id, effects);

        // THE SHARED BINDING — the producer's own turn context. No accumulator root is named here,
        // so this fixture's BEFORE witness cannot commit a different set than the producer's does.
        let receipt_hashes: Vec<[u8; 32]> = Vec::new();
        let mut ctx_ledger = Ledger::new();
        let _ = ctx_ledger.insert_cell(before_cell.clone());
        let turn_ctx = rw::sovereign_turn_ctx(&ctx_ledger, &receipt_hashes, Default::default());

        let before_w = turn_ctx.witness(before_cell);
        let after_w = turn_ctx.witness(bound_after);

        let initial_vm_state =
            dregg_circuit::effect_vm::CellState::with_capability_root_and_record_digest(
                u64::try_from(before_cell.state.balance()).unwrap(),
                before_cell.state.nonce() as u32,
                dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
                dregg_cell::compute_authority_digest_felt(before_cell),
            );
        let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();

        // The umem cohort the deployed weld reconciles: the turn's GENUINE record-kernel projection
        // diff, exactly as `cipherclerk::prove_sovereign_turn_rotated` builds it. The producer's
        // weld predicate is `!ops.is_empty() && all ops share one domain`; a fixture that fell
        // outside it would mint a BARE leg and be refused on routing, so both halves are asserted
        // here rather than discovered as a mysterious verify failure.
        let pre = project_record_kernel_state(before_cell);
        let post = project_record_kernel_state(umem_after);
        let ops = project_diff_ops(&pre, &post);
        assert!(
            !ops.is_empty(),
            "the umem cohort diff is EMPTY, so the deployed producer would mint the BARE wide leg \
             and the executor would refuse it on routing — not on any anchor"
        );
        let domain = ops[0].key.domain();
        assert!(
            ops.iter().all(|op| op.key.domain() == domain),
            "the umem cohort diff spans more than one domain ({:?}), which the single-domain cohort \
             weld refuses — the deployed producer would fall back to the BARE wide leg",
            ops.iter().map(|op| op.key.domain()).collect::<Vec<_>>()
        );

        // THE REFUSAL `fields_root` WRITE-GATE CONTEXT (the deployed prover wire). A Refusal lead's
        // member carries an in-circuit `.write` map-op forcing
        // `after_fields_root == write(before_fields_root, REFUSAL_AUDIT_KEY -> audit_felt)`, so the
        // audit value must be the one the BOUND after-block actually carries — on the forged pole
        // that is the FORGED audit, which is what makes the forged trace internally consistent and
        // pushes the verdict onto the record-digest anchor at verify time rather than onto the
        // write gate at prove time.
        let refusal_fields: Option<(
            Vec<dregg_circuit::openable_fields_root::ExactFieldsLeaf>,
            [u8; 32],
        )> = if matches!(
            vm_effects.first(),
            Some(dregg_circuit::effect_vm::Effect::Refusal { .. })
        ) {
            let leaves = dregg_cell::state::exact_fields_root_leaves(&before_cell.state.fields_map);
            let audit = bound_after
                .state
                .fields_map
                .get(&dregg_cell::state::REFUSAL_AUDIT_EXT_KEY)
                .copied()
                .expect("the bound after-cell carries a refusal audit slot in fields_map");
            Some((leaves, audit))
        } else {
            None
        };

        let (proof, wide_dpis) = prove_wide_umem_welded_staged(
            &initial_vm_state,
            &vm_effects,
            &before_w,
            &after_w,
            &caveat,
            &pre,
            &ops,
            // This fixture threads no nullifier-set context (empty grow-gate accumulator) — the
            // same `None` the cipherclerk's welded arm passes.
            None,
            refusal_fields.as_ref().map(|(l, a)| (l.as_slice(), *a)),
            // NO published turn identity: this leg goes into `turn.execution_proof`, whose verifier
            // RECONSTRUCTS the whole PI vector from the trusted `Turn`. Publishing a felt the
            // reconstruction does not also write breaks Fiat-Shamir on every honest leg.
            None,
        )?;

        let proof_bytes = postcard::to_allocvec(&proof).expect("serialize welded proof");

        // ⚑ THE FAITHFUL 8-FELT CLAIM, READ OFF THE PROOF'S OWN PI TAIL — the deployed producer's
        // derivation, byte-for-byte (`cipherclerk::prove_sovereign_turn_rotated`:
        // `felt8_to_bytes32(&public_inputs[n_pi - 8..n_pi])`). The last 16 wide PIs are the BEFORE
        // then AFTER 8-felt commit anchors, and the executor reads this 32-byte slot back through
        // `bytes32_to_felt8` to bind them.
        //
        // ⚠ What stood here — `felt_to_bytes32(commitment_felt(after))` — was a THIRD shared refusal
        // cause hiding behind the same `Rejected` arm as the bare-prover routing one. That is the
        // 1-felt `wireCommitR` in bytes `0..4` with 28 zero bytes after it, while the ledger stores
        // `commitment_8` and the verifier anchors 8 felts: every leg this module minted disagreed
        // with the verifier on the AFTER anchors no matter what it proved.
        //
        // ⚑ And publishing the proof's OWN tail is what makes the forgery a real one. The AFTER
        // commitment is a PROVER CLAIM on the deployed path by construction; the executor's teeth
        // are the BEFORE anchor against the ledger's stored commitment and the record-pin anchor
        // recomputed from the trusted pre-cell. A forger publishes the commitment their forged proof
        // binds — so the commitment chain does NOT catch them and only the anchor can, which is
        // exactly the claim each of these tests makes.
        //
        // ⚠ ⚑ **AND THE TWO DERIVATIONS ARE NOT THE SAME OBJECT — MEASURED, 2026-08-08.** Over all
        // eight record-pin members the published BEFORE tail equals `commitment_8(before_cell)`
        // **8/8**, but the published AFTER tail equals `commitment_8(honest_after)` for only **1 of
        // 8** (`refusalVmDescriptor2R24`). So on the record-pin family the cell-side v9 fold and the
        // wide proof's AFTER carrier are TWO FUNCTIONS FOR ONE DENOTATION. The deployed producer is
        // on the right side of it (it reads the PI tail), and the cipherclerk's own cross-check
        // `debug_assert_eq!` covers the BEFORE half ONLY — which is precisely why nothing has been
        // shouting about the AFTER half. A named residual, out of this driver's scope: it is a
        // producer/commitment question, not a test question, and repairing it moves the AFTER commit
        // an honest turn publishes.
        let n_pi = wide_dpis.len();
        assert!(
            n_pi >= 16,
            "the wide PI vector must carry the 16-felt before/after commit tail, got {n_pi}"
        );
        let after_commit_8: [BabyBear; 8] = wide_dpis[n_pi - 8..n_pi]
            .try_into()
            .expect("the wide PI tail carries 8 AFTER commit felts");
        let new_commitment = dregg_cell::commitment::felt8_to_bytes32(&after_commit_8);
        Ok((proof_bytes, new_commitment, wide_dpis))
    }

    /// Assemble the proof-carrying turn the deployed executor consumes (the cipherclerk producer's
    /// turn shape, minus the signature leg — the authority IS the attached proof).
    fn proof_carrying_turn(
        cell_id: dregg_cell::CellId,
        effects: &[Effect],
        proof_bytes: Vec<u8>,
        new_commitment: [u8; 32],
    ) -> Turn {
        let mut forest = dregg_turn::forest::CallForest::new();
        let action = dregg_sdk::raw::unsigned_action_named(
            cell_id,
            "sovereign_execute_proven",
            effects.to_vec(),
        );
        forest.add_root(action);
        Turn {
            agent: cell_id,
            nonce: 0,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: Some(proof_bytes),
            execution_proof_cell: Some(cell_id),
            execution_proof_new_commitment: Some(new_commitment),
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// ⚑ **THE HONEST POLE OF THE FORGE DRIVER** — prove the HONEST after-block through the SAME
    /// welded prover the forgery uses and drive it all the way to `Committed` through the executor,
    /// on a CLONE of the ledger, BEFORE any verdict is read off the forgery.
    ///
    /// Without it `assert_forged_after_rejected` cannot tell a correctly-refusing member from a
    /// BROKEN one: every arm of that driver — the prove-time refusal, the `Rejected` match — is
    /// satisfied just as well by a member that refuses EVERYTHING. That is exactly the state this
    /// repair found the tree in twice over: the bare-prover routing refusal, and a 1-felt
    /// `execution_proof_new_commitment` that could never anchor the wide AFTER PIs. Either alone is
    /// enough to make every forgery here "pass" while measuring one thing.
    ///
    /// ⚑ Do not delete this to reach green. A forge test that cannot commit an honest turn is
    /// indistinguishable from a broken member.
    ///
    /// The ledger it mutates is a clone, so the forgery below still meets the untouched
    /// registration state.
    fn assert_honest_pole_commits(
        cell_id: dregg_cell::CellId,
        before_cell: &Cell,
        effects: &[Effect],
        honest_after: &Cell,
        ledger: &Ledger,
        block_height: u64,
        what: &str,
    ) {
        let (proof_bytes, new_commitment, dpis) =
            mint_welded_leg(cell_id, before_cell, effects, honest_after, honest_after)
                .unwrap_or_else(|e| {
                    panic!(
                        "{what}: THE HONEST POLE IS UNPROVABLE ({e}). The paired forgery assertion \
                         below is therefore vacuous — it would 'reject' every witness, honest or not."
                    )
                });

        // ⚑ **THE BEFORE ANCHOR IS THE LEDGER'S OWN REGISTRATION, NOT A SECOND DERIVATION.** The
        // ledger holds `sovereign_registration_commitment(before_cell, &[])` — i.e.
        // `SovereignTurnCtx::commitment_8` — and the executor reads it back through
        // `bytes32_to_felt8` as this leg's 8 BEFORE commit PIs. Pinning that it EQUALS what the
        // proof published is what makes the `InvalidPowWitness` the forgery earns readable: the
        // BEFORE half of the transcript is established as agreeing, so the divergence the forgery
        // produces is on the after-block and the anchored record-pin PI, not on the fixture's idea
        // of the pre-state.
        //
        // ⚠ **AND THE AFTER HALF DOES *NOT* AGREE, WHICH IS A FINDING, NOT A CONVENIENCE.** Measured
        // over all eight members: `commitment_8(before_cell)` EQUALS the published BEFORE tail 8/8,
        // while `commitment_8(honest_after)` DIFFERS from the published AFTER tail for **7 of the 8**
        // (`refusalVmDescriptor2R24` is the lone agreement). So the cell-side v9 fold and the wide
        // proof's AFTER carrier are two functions for one denotation on the record-pin family, and
        // anything deriving `execution_proof_new_commitment` from the cell-side fold publishes a
        // commitment the verifier refuses. The deployed producer reads the PI tail
        // (`cipherclerk::prove_sovereign_turn_rotated`), which is why the live path works and why
        // this fixture now does the same. See this module's `mint_welded_leg` docblock.
        {
            let n = dpis.len();
            let published_before = dregg_cell::commitment::felt8_to_bytes32(
                &<[dregg_circuit::field::BabyBear; 8]>::try_from(&dpis[n - 16..n - 8])
                    .expect("the wide PI tail carries 8 BEFORE commit felts"),
            );
            let stored = ledger
                .get_sovereign_commitment(&cell_id)
                .copied()
                .expect("the fixture registered a sovereign commitment for this cell");
            assert_eq!(
                stored, published_before,
                "{what}: the ledger's registered OLD commitment is not the one this leg published \
                 at its BEFORE anchor — the fixture and the producer disagree about the pre-state, \
                 so every verdict below would be about THAT, not about the forgery"
            );
        }

        let turn = proof_carrying_turn(cell_id, effects, proof_bytes, new_commitment);

        let mut honest_ledger = ledger.clone();
        let mut executor = TurnExecutor::new(ComputronCosts::zero());
        // The SAME height the honest post-state was built at. The verifier's record-pin anchor
        // recomputes `apply_effect_to_cell(trusted pre, lead, self.block_height)`, so a driver
        // sitting at height 0 while the fixture sealed at 42 would reject the HONEST turn on the
        // seal timestamp and call it "the anchor".
        executor.set_block_height(block_height);
        match executor.execute(&turn, &mut honest_ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!(
                "{what}: THE HONEST POLE WAS REJECTED ({other:?}). The paired forgery assertion below \
                 is therefore vacuous — the member refuses everything, which is indistinguishable \
                 from refusing the forgery."
            ),
        }
        let committed = honest_ledger
            .get_sovereign_commitment(&cell_id)
            .expect("sovereign commitment present after the honest commit");
        assert_eq!(
            *committed, new_commitment,
            "{what}: the honest pole committed a commitment other than the one it proved"
        );
    }

    /// **THE VERIFY-POLE VERDICT DISCRIMINATOR** — the executor rejected, but *what* rejected it?
    ///
    /// `TurnResult::Rejected` is satisfied by every failure mode this module has now hit three
    /// separate times, so the string is read rather than counted:
    ///
    ///   * ⛔ a ROUTING refusal — *"proof bound NO descriptor … bare wide DROPPED (welded required —
    ///     G4 flip) … IR v2 proof carries 3 instances but the descriptor's present-table set is 5"*.
    ///     The leg never reached this member's constraint system at all. This is what six forge
    ///     tests were reading as six different anchors before `2fd097812`.
    ///   * ⛔ a SHAPE/ARITY complaint — the prover's pre-flight refusing the trace's GEOMETRY,
    ///     `refusal::SHAPE_FAULT_MARKERS`. The witness was never examined.
    ///   * ⛔ a BUS imbalance (`LookupError` / `Lookup mismatch`) — some LogUp multiset failed to
    ///     cancel. A bus is not an anchor; if a forged record-pin limb were caught by the bus, some
    ///     lookup and not the anchor would be what binds it.
    ///   * ✅ a CONSTRAINT verdict (`OodEvaluationMismatch` / p3's `constraints not satisfied on
    ///     row N`), or
    ///   * ✅ `InvalidOpeningArgument(InvalidPowWitness)` — the FIAT–SHAMIR transcript refusing.
    ///
    /// ⚑ **Why the transcript refusal counts, and only here.** The record-pin anchor is an
    /// *anchored PUBLIC INPUT*: `verify_one_cohort_run` overwrites `dpis[ROT_PI_COUNT..]` with the
    /// forced limb it recomputes from the TRUSTED pre-cell (`compute_authority_digest_8` /
    /// `lifecycle_felt_cell` of `apply_effect_to_cell(pre, lead, block_height)`) before it verifies.
    /// Public inputs are absorbed into the transcript BEFORE the challenges are drawn, so a
    /// forged-after whose bound limb differs from the anchor makes the verifier derive different
    /// challenges than the prover did — and the grinding witness fails before a single constraint is
    /// evaluated. `OodEvaluationMismatch` is structurally UNREACHABLE for this class of forgery. It
    /// is the strictly stronger refusal, not a weaker one: the proof cannot even be opened.
    ///
    /// ⚠ And `InvalidPowWitness` is admissible ONLY because the honest pole ran first. On its own it
    /// says "some absorbed value disagreed", which is equally true of a fixture that disagrees with
    /// the verifier about an unrelated PI — exactly the state this module was in an hour ago, when
    /// all eight honest poles returned this same string. What makes it readable as *the anchor* is
    /// that the honest witness, differing from the forgery in the after-BLOCK and nothing else,
    /// proved and COMMITTED through this same executor.
    fn assert_anchor_refusal(member: AnchorMember, s: &str, what: &str) {
        use dregg_circuit::refusal::{
            BUS_REFUSAL_MARKERS, CONSTRAINT_REFUSAL_MARKERS, shape_fault,
        };
        let flavor = member.flavor;
        let welded = member.welded_wire_name();

        assert!(
            s.contains(welded),
            "{what}: the refusal does not name the member this test is about ({}, welded twin \
             `{welded}`) — so it is not this anchor biting: {s}",
            member.key
        );
        assert!(
            !s.contains("present-table set"),
            "{what}: this is the ROUTING refusal (the leg's committed table set does not even match \
             the member's), not the {flavor:?} anchor — the forgery was never examined: {s}"
        );
        if let Some(m) = shape_fault(s) {
            panic!(
                "{what}: the refusal is a SHAPE/ARITY fault ({m:?}), so the constraint system never \
                 examined the forged witness — this tooth witnessed nothing: {s}"
            );
        }
        assert!(
            !BUS_REFUSAL_MARKERS.iter().any(|m| s.contains(m)),
            "{what}: refused by a BUS IMBALANCE, not by the {flavor:?} record-pin anchor this test \
             names: {s}"
        );
        let constraint = CONSTRAINT_REFUSAL_MARKERS.iter().any(|m| s.contains(m));
        let transcript = s.contains("InvalidPowWitness");
        assert!(
            constraint || transcript,
            "{what}: the executor rejected, but its message names neither a constraint verdict \
             {CONSTRAINT_REFUSAL_MARKERS:?} nor the anchored-PI transcript refusal \
             (`InvalidPowWitness`) — so it is not the {flavor:?} anchor biting: {s}"
        );
    }

    /// SHARED FORGED-AFTER DRIVER — one per record-pin anchor, and each one must fail for ITS OWN
    /// reason.
    ///
    /// The turn's vm-effects are HONEST (so every PI the verifier reconstructs from the trusted
    /// `Turn` matches by construction) and so is the universal-memory leg; the ONLY thing forged is
    /// the AFTER block, whose forced limb is `member.flavor.felt(forged_after)`. The driver then:
    ///
    ///   1. **localizes the plant** — it moves the limb this test names and leaves the SIBLING limb
    ///      untouched, so a refusal cannot be attributed to the other anchor;
    ///   2. **pins the routing** — the deployed producer's own `rotated_descriptor_name_for_effect`
    ///      resolves this member's registry KEY for this lead;
    ///   3. **exhibits the honest pole** — the honest after-block proves AND commits;
    ///   4. **reads the verdict** — through `refusal::classify` (the primitive
    ///      `must_refuse_or_unsat_panic` is built from; this driver needs the `Accepted` arm too,
    ///      because half these forgeries legitimately PROVE and are caught one layer down) plus
    ///      `assert_violated_constraint_not_bus`, so a bus imbalance is never counted as an anchor
    ///      biting, and — where the refusal lands at verify — the executor's message must NAME this
    ///      member's welded wire name.
    ///
    /// Two refusal poles are legitimate and the driver discriminates between them rather than
    /// swallowing both:
    ///
    ///   * **PROVE-TIME UNSAT** — a plant whose lifecycle DISCRIMINANT or mode byte contradicts the
    ///     effect's mandated transition violates the member's own in-circuit gate
    ///     (`rotateV3WithDiscGate` / the makeSovereign mode gate), so the welded trace cannot close.
    ///     This is the STRONGER refusal: unprovable for a ledgerless client, no trusted post-cell.
    ///   * **VERIFY-TIME ANCHOR** — a plant whose disc is unchanged but whose PAYLOAD differs (a
    ///     wrong death certificate, a wrong refusal audit) proves fine, and the executor's
    ///     record-pin anchor rejects it: the anchored PI disagrees with the proof's bound forced
    ///     column ⇒ UNSAT against this member.
    #[allow(clippy::too_many_arguments)]
    fn assert_forged_after_rejected(
        cell_id: dregg_cell::CellId,
        before_cell: &Cell,
        effects: &[Effect],
        honest_after: &Cell,
        forged_after: &Cell,
        member: AnchorMember,
        mut ledger: Ledger,
        block_height: u64,
        what: &str,
    ) {
        use dregg_circuit::refusal::{Outcome, assert_violated_constraint_not_bus, classify};

        let flavor = member.flavor;

        // 1. THE PLANT IS LOCALIZED TO THE LIMB THIS TEST NAMES.
        assert_ne!(
            flavor.felt(forged_after),
            flavor.felt(honest_after),
            "{what}: the forgery must move the forced limb off the honest post-value (the bite witness)"
        );
        assert_eq!(
            flavor.sibling().felt(forged_after),
            flavor.sibling().felt(honest_after),
            "{what}: this plant ALSO moved the {:?} limb, so a refusal here would not be \
             attributable to the {flavor:?} anchor this test names",
            flavor.sibling()
        );

        // 2. THE ROUTING: the deployed producer resolves THIS member's key for this lead.
        let vm_effects = AgentCipherclerk::convert_effects_to_vm(&cell_id, effects);
        let lead = vm_effects
            .first()
            .unwrap_or_else(|| panic!("{what}: the turn projects no vm-effect"));
        member.assert_routes(lead, what);

        // 3. THE HONEST POLE FIRST, ALWAYS. Every rejection arm below is also satisfied by a broken
        //    member, so no verdict may be read off the forgery until the honest witness has proved
        //    AND committed.
        assert_honest_pole_commits(
            cell_id,
            before_cell,
            effects,
            honest_after,
            &ledger,
            block_height,
            what,
        );

        // 4. THE FORGERY. The umem leg is the HONEST one (see `mint_welded_leg`) so the ONLY
        //    difference from the pole above is the after-BLOCK.
        let minted: Outcome<
            (Vec<u8>, [u8; 32], Vec<dregg_circuit::field::BabyBear>),
            dregg_sdk::SdkError,
        > = classify(what, || {
            mint_welded_leg(cell_id, before_cell, effects, forged_after, honest_after)
        });
        let (proof_bytes, new_commitment, _fdpis) = match minted {
            Outcome::Accepted(v) => v,
            // PROVE-TIME UNSAT — the member's own in-circuit gate refused the forged trace.
            Outcome::Err(e) => {
                let reason = format!("{e:?}");
                assert_violated_constraint_not_bus(
                    &format!("{what} (prove-time, {})", member.key),
                    &reason,
                );
                eprintln!(
                    "{what}: REFUSED AT PROVE TIME by the in-circuit gate of {} \
                     ({}) — the forgery is unprovable for a ledgerless client (no trusted \
                     post-cell, no anchor needed). Reason: {reason}",
                    member.key,
                    member.welded_wire_name()
                );
                return;
            }
            Outcome::UnsatPanic(m) => {
                assert_violated_constraint_not_bus(
                    &format!("{what} (prove-time, {})", member.key),
                    &m,
                );
                eprintln!(
                    "{what}: REFUSED AT PROVE TIME by the in-circuit gate of {} ({}) — p3's unsat \
                     verdict: {m}",
                    member.key,
                    member.welded_wire_name()
                );
                return;
            }
        };

        // 5. THE FORGED LEG CLOSED — so the verdict must come from the executor's record-pin anchor,
        //    and it must NAME this member.
        let turn = proof_carrying_turn(cell_id, effects, proof_bytes, new_commitment);
        let mut executor = TurnExecutor::new(ComputronCosts::zero());
        executor.set_block_height(block_height);
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Rejected { reason, .. } => {
                let s = format!("{reason:?}");
                assert_anchor_refusal(member, &s, what);
                eprintln!(
                    "{what}: REFUSED AT VERIFY by the {flavor:?} record-pin anchor of {} ({}). \
                     Reason: {s}",
                    member.key,
                    member.welded_wire_name()
                );
            }
            other => panic!(
                "{what}: ANTI-GHOST — a forged-after proof must be rejected by the record-pin \
                 anchor of {}, got {other:?}",
                member.key
            ),
        }
    }

    /// HONEST accept driver: produce a rotated sovereign turn via the cipherclerk (which applies the
    /// effect through the SHARED `apply_effect_to_cell`), then verify+commit through the executor.
    /// A `Committed` result exercises the anchor's ACCEPT side (without the anchor the placeholder PI
    /// 38 = 0 disagrees with the honest after-limb and the turn is REJECTED).
    fn assert_honest_accept(
        mut cclerk: AgentCipherclerk,
        cell_id: dregg_cell::CellId,
        mut ledger: Ledger,
        effects: Vec<Effect>,
        block_height: u64,
        what: &str,
    ) {
        let turn = cclerk
            .execute_sovereign_turn_with_proof(&cell_id, effects, 0, block_height)
            .unwrap_or_else(|e| panic!("{what}: honest turn should prove: {e}"));
        let mut executor = TurnExecutor::new(ComputronCosts::zero());
        executor.set_block_height(block_height);
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!("{what}: honest turn must commit, got {other:?}"),
        }
        let committed = ledger
            .get_sovereign_commitment(&cell_id)
            .expect("sovereign commitment present after commit");
        assert_eq!(
            *committed,
            turn.execution_proof_new_commitment.unwrap(),
            "{what}: the sovereign commitment must advance to the proven post-state"
        );
    }

    // ── cellSeal ────────────────────────────────────────────────────────────────────────────────

    #[test]
    fn rotated_sovereign_cell_seal_proves_and_verifies() {
        let height = 42;
        let (cclerk, cell_id, ledger, _before) = setup_with_cell(1000);
        let effects = vec![Effect::CellSeal {
            target: cell_id,
            reason: [9u8; 32],
        }];
        assert_honest_accept(cclerk, cell_id, ledger, effects, height, "cellSeal accept");
    }

    #[test]
    fn rotated_sovereign_forged_after_cell_seal_is_rejected() {
        let height = 42;
        let (_c, cell_id, ledger, before_cell) = setup_with_cell(1000);
        let effects = vec![Effect::CellSeal {
            target: cell_id,
            reason: [9u8; 32],
        }];
        // Honest after: sealed at `height` with reason [9;32].
        let mut honest_after = before_cell.clone();
        honest_after.seal([9u8; 32], height).unwrap();
        // Forged after: still Live (claims a seal that did not move the lifecycle).
        let forged_after = before_cell.clone();
        assert_forged_after_rejected(
            cell_id,
            &before_cell,
            &effects,
            &honest_after,
            &forged_after,
            AnchorMember::CELL_SEAL,
            ledger,
            height,
            "cellSeal forged-after (frozen Live)",
        );
    }

    // ── cellUnseal ──────────────────────────────────────────────────────────────────────────────

    #[test]
    fn rotated_sovereign_cell_unseal_proves_and_verifies() {
        // The before-cell is pre-Sealed (so unseal → Live is the genuine move).
        let (cclerk, cell_id, ledger, _before) =
            setup_with_mutated_cell(1000, |c| c.seal([9u8; 32], 7).unwrap());
        let effects = vec![Effect::CellUnseal { target: cell_id }];
        assert_honest_accept(cclerk, cell_id, ledger, effects, 0, "cellUnseal accept");
    }

    #[test]
    fn rotated_sovereign_forged_after_cell_unseal_is_rejected() {
        let (_c, cell_id, ledger, before_cell) =
            setup_with_mutated_cell(1000, |c| c.seal([9u8; 32], 7).unwrap());
        let effects = vec![Effect::CellUnseal { target: cell_id }];
        // Honest after: Live (unsealed).
        let mut honest_after = before_cell.clone();
        honest_after.unseal().unwrap();
        // Forged after: still Sealed (claims an unseal that did not happen).
        let forged_after = before_cell.clone();
        assert_forged_after_rejected(
            cell_id,
            &before_cell,
            &effects,
            &honest_after,
            &forged_after,
            AnchorMember::CELL_UNSEAL,
            ledger,
            0,
            "cellUnseal forged-after (frozen Sealed)",
        );
    }

    // ── cellDestroy ─────────────────────────────────────────────────────────────────────────────

    #[test]
    fn rotated_sovereign_cell_destroy_proves_and_verifies() {
        let (cclerk, cell_id, ledger, _before) = setup_with_cell(1000);
        let effects = vec![Effect::CellDestroy {
            target: cell_id,
            certificate: death_cert(cell_id),
        }];
        assert_honest_accept(cclerk, cell_id, ledger, effects, 0, "cellDestroy accept");
    }

    #[test]
    fn rotated_sovereign_forged_after_cell_destroy_is_rejected() {
        let (_c, cell_id, ledger, before_cell) = setup_with_cell(1000);
        let cert = death_cert(cell_id);
        let effects = vec![Effect::CellDestroy {
            target: cell_id,
            certificate: cert.clone(),
        }];
        // Honest after: Destroyed with `cert`.
        let mut honest_after = before_cell.clone();
        honest_after.destroy(&cert).unwrap();
        // Forged after: Destroyed with a DIFFERENT death certificate (the death-cert MUST be
        // reflected in the lifecycle felt — `lifecycle_felt` folds `death_certificate_hash`).
        let mut forged_cert = cert.clone();
        forged_cert.reason = dregg_cell::lifecycle::DeathReason::Forced;
        let mut forged_after = before_cell.clone();
        forged_after.destroy(&forged_cert).unwrap();
        assert_forged_after_rejected(
            cell_id,
            &before_cell,
            &effects,
            &honest_after,
            &forged_after,
            AnchorMember::CELL_DESTROY,
            ledger,
            0,
            "cellDestroy forged-after (wrong death-cert)",
        );
    }

    // ── receiptArchive (the re-routed #219 close) ────────────────────────────────────────────────

    #[test]
    fn rotated_sovereign_receipt_archive_proves_and_verifies() {
        let (cclerk, cell_id, ledger, _before) = setup_with_cell(1000);
        let effects = vec![Effect::ReceiptArchive {
            prefix_end_height: 5,
            checkpoint: archive_att(cell_id),
        }];
        assert_honest_accept(cclerk, cell_id, ledger, effects, 0, "receiptArchive accept");
    }

    #[test]
    fn rotated_sovereign_forged_after_receipt_archive_is_rejected() {
        let (_c, cell_id, ledger, before_cell) = setup_with_cell(1000);
        let att = archive_att(cell_id);
        let effects = vec![Effect::ReceiptArchive {
            prefix_end_height: 5,
            checkpoint: att.clone(),
        }];
        // Honest after: Archived through height 5.
        let mut honest_after = before_cell.clone();
        honest_after.archive(&att).unwrap();
        // Forged after: still Live (claims an archive that did not move the lifecycle). This is the
        // exact MIS-ROUTE the prior record-digest pin could not catch (the deployed apply moves the
        // lifecycle, NOT the record digest); the re-routed B_LIFECYCLE pin BITES.
        let forged_after = before_cell.clone();
        assert_forged_after_rejected(
            cell_id,
            &before_cell,
            &effects,
            &honest_after,
            &forged_after,
            AnchorMember::RECEIPT_ARCHIVE,
            ledger,
            0,
            "receiptArchive forged-after (frozen Live)",
        );
    }

    // ── refusal (the #218 close — apply_refusal now writes fields_root) ───────────────────────────

    #[test]
    fn rotated_sovereign_refusal_proves_and_verifies() {
        let (cclerk, cell_id, ledger, _before) = setup_with_cell(1000);
        let effects = vec![Effect::Refusal {
            cell: cell_id,
            offered_action_commitment: [7u8; 32],
            refusal_reason: dregg_turn::action::RefusalReason::Declined,
            proof_witness_index: 0,
        }];
        assert_honest_accept(cclerk, cell_id, ledger, effects, 0, "refusal accept");
    }

    #[test]
    fn rotated_sovereign_forged_after_refusal_is_rejected() {
        let (_c, cell_id, ledger, before_cell) = setup_with_cell(1000);
        let effects = vec![Effect::Refusal {
            cell: cell_id,
            offered_action_commitment: [7u8; 32],
            refusal_reason: dregg_turn::action::RefusalReason::Declined,
            proof_witness_index: 0,
        }];
        // Honest after: the refusal audit landed in fields_root (record digest moves) + nonce bumped.
        let mut honest_after = before_cell.clone();
        rw::apply_effect_to_cell(&mut honest_after, &cell_id, &effects[0], 0);
        // Forged after: a DIFFERENT refusal audit (a refusal the effect did NOT produce). We forge by
        // writing a different audit commitment into the reserved ext key, so the record digest moves
        // off the honest value.
        let mut forged_after = before_cell.clone();
        let _ = forged_after.state.increment_nonce();
        forged_after
            .state
            .set_field_ext(dregg_cell::state::REFUSAL_AUDIT_EXT_KEY, [0xEE; 32]);
        assert_forged_after_rejected(
            cell_id,
            &before_cell,
            &effects,
            &honest_after,
            &forged_after,
            AnchorMember::REFUSAL,
            ledger,
            0,
            "refusal forged-after (wrong audit)",
        );
    }

    // ── makeSovereign (the mode-promotion record-digest residual, NEWLY anchored) ─────────────────
    //
    // makeSovereign flips the cell `mode` Hosted→Sovereign; `compute_authority_digest_felt` FOLDS the
    // mode byte (`Hosted=0/Sovereign=1`), so the AFTER r23 authority-digest limb (`B_RECORD_DIGEST`)
    // MOVES on a genuine promotion. The deployed `makeSovereignVmDescriptor2R24` welds that limb to PI
    // 46, but PI 46 is a PRODUCER-SUPPLIED free PI on the light-client path UNTIL the full-node
    // verifier independently re-derives it from the trusted pre-cell + the promotion. The record-pin
    // anchor (`verify_one_cohort_run`, MakeSovereign arm) is that re-derivation: it sets PI 46 =
    // `compute_authority_digest_felt(apply_effect_to_cell(before_cell))` (= digest with mode flipped),
    // so a forged AFTER block claiming the cell stayed Hosted (the un-promoted residue) is UNSAT.
    // makeSovereign carries NO in-circuit mode weld at prove time (the record-pin anchor IS the
    // binding), so the forge proves and the rejection lands at VERIFY — no catch_unwind.

    /// Re-derive `setup_with_cell` but leave the before-cell in `Hosted` mode, so a makeSovereign
    /// promotion genuinely MOVES the folded mode byte (a Sovereign-before promotion is a no-op).
    fn setup_hosted_cell(balance: u64) -> (AgentCipherclerk, dregg_cell::CellId, Ledger, Cell) {
        let cclerk = AgentCipherclerk::new();
        let pub_key = cclerk.public_key().0;
        let token_id = *blake3::hash(b"c1-domain").as_bytes();

        let mut cell = Cell::with_balance(pub_key, token_id, i64::try_from(balance).unwrap());
        cell.mode = CellMode::Hosted;
        let cell_id = cell.id();

        // THE SHARED BINDING — the producer's own context builder, and no root is named here.
        // `sovereign_registration_commitment` takes (cell, receipt log) and nothing else.
        let commitment = rw::sovereign_registration_commitment(&cell, &[]);

        let mut cclerk = cclerk;
        cclerk.store_sovereign_state(cell.clone());

        let mut ledger = Ledger::new();
        ledger.register_sovereign_cell(cell_id, commitment).unwrap();
        let _ = ledger.insert_cell(cell.clone());

        (cclerk, cell_id, ledger, cell)
    }

    /// CONTROL + BITE: an HONEST sovereign `MakeSovereign` turn proves and verifies; the committed
    /// authority digest reflects the flipped mode. Passes ONLY because the verifier anchors PI 46 to
    /// the trusted post-cell digest (mode=Sovereign) — without the MakeSovereign anchor arm the
    /// placeholder PI 46 would disagree with the honest after-limb and REJECT this honest turn.
    #[test]
    fn rotated_sovereign_make_sovereign_proves_and_verifies() {
        let (cclerk, cell_id, ledger, before) = setup_hosted_cell(1000);
        assert_eq!(before.mode, CellMode::Hosted, "before-cell must be Hosted");
        // The promotion genuinely MOVES the folded mode byte (the bite witness).
        let mut honest_after = before.clone();
        honest_after.mode = CellMode::Sovereign;
        assert_ne!(
            dregg_cell::compute_authority_digest_felt(&honest_after),
            dregg_cell::compute_authority_digest_felt(&before),
            "the promotion must move the authority digest (the folded mode byte flips)"
        );
        let effects = vec![Effect::MakeSovereign { cell: cell_id }];
        assert_honest_accept(cclerk, cell_id, ledger, effects, 0, "makeSovereign accept");
    }

    /// ANTI-GHOST (the makeSovereign forgery is REJECTED): a proof whose AFTER block claims the cell
    /// stayed Hosted (the un-promoted authority residue) — which the promotion did NOT produce — is
    /// rejected. makeSovereign carries an IN-CIRCUIT mode-transition gate (the deployed
    /// `makeSovereignVmDescriptor2R24`'s first constraint forces `B_MODE_after = B_MODE_before + 256`,
    /// i.e. Hosted→Sovereign), so a forged un-promoted after-block is UNSAT at PROVE time — the
    /// STRONGEST rejection (unprovable for a ledgerless client, no trusted post-cell needed). The
    /// PI-46 record-pin anchor I wired in `verify_one_cohort_run` is the BELT-AND-SUSPENDERS full-node
    /// leg for the folded authority residue (parallel to setPerms/setVK): on the rare forge whose mode
    /// disc IS satisfied but whose opaque residue differs, the anchor catches it at verify. The shared
    /// `assert_forged_after_rejected` driver handles BOTH poles (prove-time-unprovable OR verify-time
    /// anchor), so this uses it directly — matching the lifecycle/setVK forge tests.
    #[test]
    fn rotated_sovereign_forged_after_make_sovereign_is_rejected() {
        let (_c, cell_id, ledger, before_cell) = setup_hosted_cell(1000);
        let effects = vec![Effect::MakeSovereign { cell: cell_id }];
        // Honest after: mode flipped to Sovereign (the folded authority residue moves).
        let mut honest_after = before_cell.clone();
        honest_after.mode = CellMode::Sovereign;
        // Forged after: still Hosted (claims a promotion that did NOT move the mode/residue). The
        // in-circuit mode gate makes this un-promoted after-block UNSAT at prove time.
        let forged_after = before_cell.clone();
        assert_forged_after_rejected(
            cell_id,
            &before_cell,
            &effects,
            &honest_after,
            &forged_after,
            AnchorMember::MAKE_SOVEREIGN,
            ledger,
            0,
            "makeSovereign forged-after (un-promoted Hosted)",
        );
    }
}

// ===========================================================================
// THE WHOLE-TURN FOREST TOOTH (foolable gap #2, the LIVE-WIRE of
// `RotatedKernelForestCohortChain.lean`). A heterogeneous sovereign turn
// `[Transfer, SetPermissions]` splits into TWO maximal homogeneous cohort runs. The chained
// producer (`prove_sovereign_cohort_chain`) mints ONE rotated leg per run + threads the per-run
// 8-felt commit into a `SovereignCohortChain`; the deployed executor leg
// (`verify_and_commit_proof_rotated`) verifies EVERY leg + chains them (leg[0].before == stored OLD,
// leg[N-1].after == claimed NEW, leg[i+1].before == leg[i].after). These tests prove the WHOLE
// forest is FORCED, not just the lead:
//   * `multi_cohort_turn_proves_and_verifies` — the HONEST 2-cohort turn proves + commits.
//   * `multi_cohort_tail_leg_omitted_is_rejected` — dropping the SetPermissions tail leg is REJECTED
//     by the chain length / adjacency check (NO executor trust — the prior `effects.first()`-only
//     verifier would have happily accepted the lead-only proof and left the tail unforced).
//   * `multi_cohort_tail_leg_unchained_is_rejected` — corrupting the tail leg's `before8` so it does
//     NOT chain off the Transfer's `after8` is REJECTED by the adjacency check.
// ===========================================================================
mod whole_turn_forest {
    use dregg_cell::{Cell, CellId, CellMode, Ledger, Permissions};
    use dregg_sdk::AgentCipherclerk;
    use dregg_turn::executor::SovereignCohortChain;
    use dregg_turn::rotation_witness as rw;
    use dregg_turn::{ComputronCosts, Effect, TurnExecutor, TurnResult};

    /// Register a sovereign cell + a dest cell for an outgoing transfer; return the live cipherclerk,
    /// the sovereign cell id, the dest id, and the ledger (the executor's view).
    fn setup() -> (AgentCipherclerk, CellId, CellId, Ledger) {
        let cclerk = AgentCipherclerk::new();
        let pub_key = cclerk.public_key().0;
        let token_id = *blake3::hash(b"c1-domain").as_bytes();
        let mut cell = Cell::with_balance(pub_key, token_id, 1000);
        cell.mode = CellMode::Sovereign;
        let cell_id = cell.id();

        // THE SHARED BINDING — the producer's own context builder, and no root is named here.
        let commitment = rw::sovereign_registration_commitment(&cell, &[]);

        let mut cclerk = cclerk;
        cclerk.store_sovereign_state(cell.clone());

        let mut ledger = Ledger::new();
        ledger.register_sovereign_cell(cell_id, commitment).unwrap();
        let _ = ledger.insert_cell(cell);

        let dest = Cell::with_balance([44u8; 32], token_id, 0);
        let dest_id = dest.id();
        let _ = ledger.insert_cell(dest);

        (cclerk, cell_id, dest_id, ledger)
    }

    fn two_cohort_effects(cell_id: CellId, dest_id: CellId) -> Vec<Effect> {
        vec![
            Effect::Transfer {
                from: cell_id,
                to: dest_id,
                amount: 100,
            },
            Effect::SetPermissions {
                cell: cell_id,
                new_permissions: Permissions::zkapp(),
            },
        ]
    }

    /// CONTROL: an HONEST 2-cohort `[Transfer, SetPermissions]` sovereign turn proves as a chain of
    /// two rotated legs and the deployed executor verifies BOTH + commits to the chained NEW.
    #[test]
    fn multi_cohort_turn_proves_and_verifies() {
        let (mut cclerk, cell_id, dest_id, mut ledger) = setup();
        let effects = two_cohort_effects(cell_id, dest_id);

        let turn = cclerk
            .execute_sovereign_turn_with_proof(&cell_id, effects, 0, 0)
            .expect("2-cohort sovereign turn should prove as a chain");

        // The wire is the multi-leg chain (NOT a bare Ir2BatchProof) with exactly two legs.
        let chain: SovereignCohortChain =
            postcard::from_bytes(turn.execution_proof.as_ref().expect("execution_proof"))
                .expect("multi-cohort turn carries the SovereignCohortChain wire");
        assert_eq!(chain.legs.len(), 2, "two cohort runs ⇒ two legs");
        // The chain is internally adjacent: leg[1].before == leg[0].after.
        assert_eq!(
            chain.legs[1].before8, chain.legs[0].after8,
            "the producer threads the interior boundary commit"
        );

        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!(
                "honest 2-cohort turn must commit through the deployed verifier, got {other:?}"
            ),
        }
        let committed = ledger
            .get_sovereign_commitment(&cell_id)
            .expect("commitment present after commit");
        assert_eq!(*committed, turn.execution_proof_new_commitment.unwrap());
    }

    /// ANTI-GHOST (the forest bites): DROP the SetPermissions tail leg. The chain then has ONE leg but
    /// the turn splits into TWO cohort runs — the deployed verifier rejects on the length/coverage
    /// check. NO executor trust: the lead Transfer leg is internally valid, yet the turn is rejected
    /// because the tail cohort's transition is NOT covered (the gap the prior `effects.first()`-only
    /// verifier left open).
    #[test]
    fn multi_cohort_tail_leg_omitted_is_rejected() {
        let (mut cclerk, cell_id, dest_id, mut ledger) = setup();
        let effects = two_cohort_effects(cell_id, dest_id);
        let mut turn = cclerk
            .execute_sovereign_turn_with_proof(&cell_id, effects, 0, 0)
            .expect("2-cohort sovereign turn should prove");

        let mut chain: SovereignCohortChain =
            postcard::from_bytes(turn.execution_proof.as_ref().unwrap()).unwrap();
        chain.legs.truncate(1); // DROP the SetPermissions tail leg.
        turn.execution_proof = Some(postcard::to_allocvec(&chain).unwrap());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Rejected { reason, .. } => {
                let s = format!("{reason:?}");
                assert!(
                    s.contains("cohort") || s.contains("forest") || s.contains("not covered"),
                    "expected a whole-forest coverage rejection, got: {s}"
                );
            }
            other => panic!(
                "ANTI-GHOST: a turn whose tail cohort proof is OMITTED must be rejected by the \
                 deployed verifier, got {other:?}"
            ),
        }
    }

    /// ANTI-GHOST (the chain bites): keep both legs but corrupt the tail leg's `before8` so it no
    /// longer chains off the Transfer leg's `after8`. The deployed verifier's adjacency check rejects
    /// (a spliced/unchained tail — the executor never trusts the interior boundary).
    #[test]
    fn multi_cohort_tail_leg_unchained_is_rejected() {
        let (mut cclerk, cell_id, dest_id, mut ledger) = setup();
        let effects = two_cohort_effects(cell_id, dest_id);
        let mut turn = cclerk
            .execute_sovereign_turn_with_proof(&cell_id, effects, 0, 0)
            .expect("2-cohort sovereign turn should prove");

        let mut chain: SovereignCohortChain =
            postcard::from_bytes(turn.execution_proof.as_ref().unwrap()).unwrap();
        // Break adjacency: the tail leg's before-anchor no longer equals the lead's after-anchor.
        chain.legs[1].before8[0] += dregg_circuit::field::BabyBear::new(1);
        turn.execution_proof = Some(postcard::to_allocvec(&chain).unwrap());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Rejected { reason, .. } => {
                let s = format!("{reason:?}");
                assert!(
                    s.contains("adjacency")
                        || s.contains("chain")
                        || s.contains("ProofVerificationFailed"),
                    "expected a chain-adjacency rejection, got: {s}"
                );
            }
            other => panic!(
                "ANTI-GHOST: a turn whose tail cohort is UNCHAINED must be rejected by the deployed \
                 verifier, got {other:?}"
            ),
        }
    }
}

// ===========================================================================
// WALL A — the rotated `prove_full_turn` / `verify_full_turn` round-trip carries
// ZERO v1 dependency. These drive `prove_full_turn` DIRECTLY with a rotation
// witness (not the executor-mint path) so the rotated leg's vk_hash (A.1) and the
// rotated-PI conservation read (A.2) are exercised, and so the v1 trace is NOT
// generated on the rotated path (A.3). The witness is built mirroring the
// cipherclerk's validated reference shape (a single outgoing sovereign transfer,
// the transfer caveat manifest).
// ===========================================================================
mod wall_a {
    use dregg_cell::{Cell, CellMode, Ledger};
    use dregg_circuit::effect_vm::{self, CellState};
    use dregg_sdk::full_turn_proof::{
        ConservationWitness, FullTurnWitness, RotationTurnWitness, prove_full_turn,
        verify_full_turn,
    };
    use dregg_turn::rotation_witness as rw;

    /// Build a valid rotated `FullTurnWitness` for a single outgoing transfer of `amount`
    /// from a sovereign cell of `balance`. Returns `(witness, old_commit_felt,
    /// new_commit_felt)` — the latter two are the rotated PI 34/35 the verifier expects.
    /// Mirrors `AgentCipherclerk::prove_sovereign_turn_rotated` (the C1 reference).
    fn build_rotated_transfer_witness(
        balance: u64,
        amount: u64,
    ) -> (
        FullTurnWitness,
        [dregg_circuit::field::BabyBear; 8],
        [dregg_circuit::field::BabyBear; 8],
    ) {
        let token_id = *blake3::hash(b"wallA-domain").as_bytes();
        let mut before_cell = Cell::with_balance([7u8; 32], token_id, balance as i64);
        before_cell.mode = CellMode::Sovereign;

        // after-state: an outgoing transfer debits the balance.
        let mut after_cell = before_cell.clone();
        after_cell
            .state
            .set_balance(after_cell.state.balance().saturating_sub(amount as i64));

        // circuit pre-state (cap-root-seeded), identical to the v1 path.
        let initial_vm_state = CellState::with_capability_root(
            before_cell.state.balance() as u64,
            before_cell.state.nonce() as u32,
            dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        );

        let vm_effects = vec![effect_vm::Effect::Transfer {
            amount,
            direction: 1, // outgoing
        }];

        // THE SHARED BINDING — the producer's own turn context. No accumulator root is named here,
        // so this fixture's BEFORE witness cannot commit a different set than the producer's does.
        let receipt_hashes: Vec<[u8; 32]> = Vec::new();
        let mut ctx_ledger = Ledger::new();
        let _ = ctx_ledger.insert_cell(before_cell.clone());
        let turn_ctx = rw::sovereign_turn_ctx(&ctx_ledger, &receipt_hashes, Default::default());

        let before_w = turn_ctx.witness(&before_cell);
        let after_w = turn_ctx.witness(&after_cell);

        let rotation = RotationTurnWitness::for_effects(before_w, after_w, &vm_effects);

        // WIDE FLAG-DAY: the trusted 8-felt (~124-bit) commit anchors `verify_full_turn` binds, the
        // SAME `wire_commit_8` before/after commits the wide producer publishes at the rotated leg's
        // PI tail. Derived from the rotation witness before it MOVES into the FullTurnWitness.
        let (old_commit, new_commit) = rotation
            .wide_commit_anchors(&initial_vm_state, &vm_effects, None)
            .expect("wide_commit_anchors");

        let witness = FullTurnWitness {
            initial_cell_state: initial_vm_state,
            effects: vm_effects,
            membership: None,
            conservation: None,
            spent_nullifiers: None,
            cap_membership: None,
            turn_hash: *blake3::hash(b"wallA-turn").as_bytes(),
            rotation: Some(rotation),
            umem_witness: None,
        };
        (witness, old_commit, new_commit)
    }

    /// CONTROL: a rotated full-turn proves through `prove_full_turn` and `verify_full_turn`
    /// ACCEPTS it — the rotated leg's vk_hash is the rotated cohort descriptor's fingerprint
    /// (A.1) and is re-checked at verify; the v1 effect-vm trace was never generated (A.3).
    #[test]
    fn rotated_full_turn_round_trips() {
        let (witness, old_commit, new_commit) = build_rotated_transfer_witness(1000, 100);
        let proof = prove_full_turn(&witness).expect("rotated full-turn should prove");

        // The attached leg is the rotated one (not the v1 "effect-vm").
        let labels: Vec<&str> = proof
            .composed
            .sub_proofs
            .iter()
            .map(|sp| sp.label.as_str())
            .collect();
        assert!(
            labels.contains(&"effect-vm-rotated"),
            "expected a rotated effect-vm leg, got {labels:?}"
        );
        assert!(
            !labels.contains(&"effect-vm"),
            "the v1 effect-vm leg must be ABSENT on the rotated path, got {labels:?}"
        );

        // WIDE FLAG-DAY: the verifier binds the rotated leg's 8-felt (~124-bit) before/after commit
        // anchors — the LAST 16 PIs of the wide leg (the `wire_commit_8` tail). Cross-check that the
        // witness-derived anchors the helper returns ARE the proof's bound PI tail, then verify.
        let rot_pi = &proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "effect-vm-rotated")
            .expect("rotated leg present")
            .sub_public_inputs;
        let n = rot_pi.len();
        assert!(
            n >= 16,
            "wide rotated leg must carry the 8-felt commit tail, got {n} PIs"
        );
        let pi_before: [dregg_circuit::field::BabyBear; 8] =
            rot_pi[n - 16..n - 8].try_into().expect("slice of len 8");
        let pi_after: [dregg_circuit::field::BabyBear; 8] =
            rot_pi[n - 8..n].try_into().expect("slice of len 8");
        assert_eq!(
            pi_before, old_commit,
            "before anchor must equal the proof's bound PI tail"
        );
        assert_eq!(
            pi_after, new_commit,
            "after anchor must equal the proof's bound PI tail"
        );

        verify_full_turn(
            &proof,
            *blake3::hash(b"wallA-turn").as_bytes(),
            old_commit,
            new_commit,
        )
        .expect("rotated full-turn should verify");
    }

    /// ANTI-GHOST (A.1): tampering the rotated leg's vk_hash is REJECTED. The verifier
    /// re-derives the expected fingerprint from the uniquely-accepting cohort descriptor and
    /// the mismatch fails — proving vk_hash is load-bearing on the rotated leg (not cosmetic).
    #[test]
    fn rotated_full_turn_tampered_vk_hash_rejected() {
        let (witness, old_commit, new_commit) = build_rotated_transfer_witness(1000, 100);
        let mut proof = prove_full_turn(&witness).expect("rotated full-turn should prove");

        let leg = proof
            .composed
            .sub_proofs
            .iter_mut()
            .find(|sp| sp.label == "effect-vm-rotated")
            .expect("rotated leg present");
        leg.vk_hash[0] ^= 0xFF; // flip a byte of the descriptor fingerprint

        let err = verify_full_turn(
            &proof,
            *blake3::hash(b"wallA-turn").as_bytes(),
            old_commit,
            new_commit,
        )
        .expect_err("ANTI-GHOST: a tampered rotated vk_hash must be rejected");
        let s = format!("{err:?}");
        assert!(
            s.contains("vk_hash") || s.contains("fingerprint"),
            "expected a vk_hash-mismatch rejection, got: {s}"
        );
    }

    /// ANTI-GHOST (A.2): with a conservation witness present, a FORGED expected_net_delta is
    /// rejected — and the check reads net_delta from the ROTATED PI (the v1 trace does not
    /// exist on this path), so this also proves the conservation leg has no v1 dependency.
    #[test]
    fn rotated_full_turn_forged_net_delta_rejected() {
        let (mut witness, _old, _new) = build_rotated_transfer_witness(1000, 100);
        // A wrong expected net_delta (the honest turn's is the outgoing-100 encoding).
        witness.conservation = Some(ConservationWitness {
            expected_net_delta: 999_999,
        });
        let err = prove_full_turn(&witness)
            .expect_err("ANTI-GHOST: a forged conservation net_delta must be rejected");
        let s = format!("{err:?}");
        assert!(
            s.contains("conservation"),
            "expected a conservation mismatch (read from the rotated PI), got: {s}"
        );
    }
}

// ===========================================================================
// THE MULTI-RESIDUE RECORD-PIN ANCHOR — #2 completeness gap: UNREACHABLE (the producer
// fails-closed). The verifier's record-pin anchor (`verify_one_cohort_run`'s PI-38 override)
// projects from the GLOBAL before-cell + the FIRST matching record-pin kernel effect (lead
// only). The concern was that a turn carrying TWO residue-moving record-pin effects on ONE
// cell would force the anchor to diverge from the producer's after-block:
//   * within-run multi-effect: `[SetPermissions(A), SetPermissions(B)]` — ONE cohort run
//     (same descriptor), the producer's after-block reflects BOTH perms (= B), the lead-only
//     anchor would project only the first (= A).
//   * cross-run residue: `[SetPermissions, CellSeal]` — TWO runs, the CellSeal leg's record-pin
//     cell would need the post-SetPermissions residue.
//
// STEP-1 (model-finds-the-bug) shows BOTH turns are UNPRODUCIBLE by the deployed `cipherclerk`
// producer: the WIDE record-pin trace's in-circuit gate (`Ir2Air` constraint #78, row 0) is
// VIOLATED at PROVE time — the panic backtrace lands in `descriptor_ir2::prove_vm_descriptor2`
// ← `prove_effect_vm_rotated_wide` ← `prove_sovereign_turn_rotated`, NEVER reaching the executor
// verifier. The deployed record-pin descriptor binds EXACTLY ONE record-pin row per cohort run;
// a second record-pin row on the same cell (a second SetPermissions, or a lifecycle move stacked
// on a record-digest move) cannot close the proof. The producer therefore CANNOT mint a turn
// that confronts the verifier's lead-only/global-cell anchor with a multi-residue run.
//
// CONCLUSION: the gap is UNREACHABLE — there is NOTHING for the deployed verifier to fix, and a
// fix would be untestable (no positive case can exist) AND would risk the live single-cohort
// fleet. The verifier (`turn/src/executor/proof_verify.rs`) is left UNCHANGED. These tests pin
// the fail-closed boundary so a future producer that lifts the one-record-pin-row limit must
// re-open the verifier anchor question (and add the positive coverage) deliberately.
// ===========================================================================
mod multi_residue_record_pin {
    use dregg_cell::{Cell, CellId, CellMode, Ledger, Permissions};
    use dregg_sdk::AgentCipherclerk;
    use dregg_turn::Effect;
    use dregg_turn::rotation_witness as rw;

    /// Register a sovereign cell; return the live cipherclerk, the sovereign cell id, the ledger.
    fn setup() -> (AgentCipherclerk, CellId, Ledger) {
        let cclerk = AgentCipherclerk::new();
        let pub_key = cclerk.public_key().0;
        let token_id = *blake3::hash(b"c1-domain").as_bytes();
        let mut cell = Cell::with_balance(pub_key, token_id, 1000);
        cell.mode = CellMode::Sovereign;
        let cell_id = cell.id();

        // THE SHARED BINDING — the producer's own context builder, and no root is named here.
        let commitment = rw::sovereign_registration_commitment(&cell, &[]);

        let mut cclerk = cclerk;
        cclerk.store_sovereign_state(cell.clone());

        let mut ledger = Ledger::new();
        ledger.register_sovereign_cell(cell_id, commitment).unwrap();
        let _ = ledger.insert_cell(cell);

        (cclerk, cell_id, ledger)
    }

    /// Drive the deployed producer over `effects` and assert it FAILS-CLOSED — either an `Err`
    /// return OR a prove-time `check_constraints` panic (the debug prover asserts on an unsatisfied
    /// constraint). A non-failing producer would mean the multi-residue turn IS minted and the
    /// verifier's lead-only/global-cell record-pin anchor would then be confronted — re-opening the
    /// #2 gap, which this test would catch.
    fn assert_producer_fails_closed(effects: Vec<Effect>, height: u64, what: &str) {
        let (mut cclerk, cell_id, _ledger) = setup();
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            cclerk.execute_sovereign_turn_with_proof(&cell_id, effects, 0, height)
        }));
        match outcome {
            // Caught the prove-time `check_constraints` panic (the observed STEP-1 fail-closed).
            Err(_) => {}
            // Returned `Err` (a softer fail-closed) — also acceptable.
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!(
                "{what}: the deployed producer MINTED a multi-residue record-pin turn — the #2 gap \
                 is now REACHABLE and the verifier's lead-only/global-cell anchor (\
                 verify_one_cohort_run) must be revisited (it would diverge from the producer's \
                 after-block). Re-open the per-run kernel-effect anchor + add positive coverage."
            ),
        }
    }

    /// within-run multi-effect: `[SetPermissions(zkapp), SetPermissions(frozen)]` is ONE cohort run
    /// (same descriptor). STEP-1 shows the deployed producer fails-closed (Ir2Air constraint #78 at
    /// prove time — the record-pin descriptor binds one record-pin row per run). UNREACHABLE.
    #[test]
    fn within_run_two_set_permissions_is_unproducible() {
        let (_c, cell_id, _l) = setup();
        let effects = vec![
            Effect::SetPermissions {
                cell: cell_id,
                new_permissions: Permissions::zkapp(),
            },
            Effect::SetPermissions {
                cell: cell_id,
                new_permissions: Permissions::frozen(),
            },
        ];
        assert_producer_fails_closed(effects, 0, "within-run 2×SetPermissions");
    }

    /// cross-run residue: `[SetPermissions, CellSeal]` is TWO cohort runs. STEP-1 shows the deployed
    /// producer fails-closed at prove time (the same record-pin row constraint). UNREACHABLE.
    #[test]
    fn cross_run_set_permissions_then_seal_is_unproducible() {
        let (_c, cell_id, _l) = setup();
        let effects = vec![
            Effect::SetPermissions {
                cell: cell_id,
                new_permissions: Permissions::zkapp(),
            },
            Effect::CellSeal {
                target: cell_id,
                reason: [9u8; 32],
            },
        ];
        assert_producer_fails_closed(effects, 42, "cross-run [SetPermissions, CellSeal]");
    }
}
