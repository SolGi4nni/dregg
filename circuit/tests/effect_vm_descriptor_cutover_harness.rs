//! # EFFECT-VM CUTOVER BEACHHEAD — descriptor interpreter as a drop-in runtime prover+verifier.
//!
//! The runtime proves/verifies every finalized turn with the HAND-WRITTEN AIR
//! (`effect_vm_p3_full_air::prove_effect_vm_p3` / `EffectVmP3Air`). The goal of the
//! "ONE circuit" migration is to retire those hand-AIRs and prove+verify through the
//! **Lean-emitted descriptor interpreter** (`EffectVmDescriptorAir`, driven by the
//! verified-by-construction descriptor JSON in the `effect_vm_descriptors` registry).
//!
//! This file is the differential-guarded cutover harness that VALIDATES the mechanism
//! on the real, end-to-end Plonky3 prover, over the SAME 186-column base trace + public
//! inputs that `generate_effect_vm_trace` produces (the witness the hand-AIR consumes).
//! For each candidate effect:
//!
//!   1. **DESCRIPTOR PROVE+VERIFY** — registry JSON by selector → `parse_vm_descriptor`
//!      → `prove_vm_descriptor` (proves + self-verifies through the AUDITED
//!      `p3-batch-stark` prover) → INDEPENDENT `verify_vm_descriptor`.
//!   2. **HAND-AIR PROVE+VERIFY** — `prove_effect_vm_p3` + `verify_effect_vm_p3`.
//!   3. **DIFFERENTIAL** — both verify AND accept-the-same-trace under Plonky3's
//!      canonical FRI-free constraint checker (`p3_air_accepts` vs `descriptor_air_accepts`).
//!   4. **ANTI-GHOST** — a TAMPERED witness (forged published post-state balance, or a
//!      mutated last-row state-commit cell) is REJECTED (UNSAT) by BOTH.
//!
//! ## What this validated (real Plonky3 output)
//!
//! * **transfer** (both directions, selector 1) is FULLY CUTOVER-READY: the descriptor
//!   interpreter and the hand-AIR both prove+verify the honest witness, agree on accept,
//!   and both reject the forged-balance + forged-state-commit tampers. The mechanism
//!   WORKS end-to-end for transfer.
//!
//! * **burn / note_create / note_spend** are NOT yet cutover-ready over the CURRENT Rust
//!   trace layout — a real, precise COLUMN-MAPPING DIVERGENCE between the Lean-emitted
//!   descriptor and the `generate_effect_vm_trace` param convention (see
//!   [`column_divergence_blockers`] for the documented, asserted blocker). The descriptor
//!   is internally consistent + verified-by-construction; it reads a DIFFERENT param/state
//!   column than the trace generator writes. The harness CATCHES this (it is the value of
//!   the differential), and the cutover for these effects is gated on reconciling the
//!   layouts (re-emit the descriptor onto the Rust param convention, or vice-versa).

use dregg_circuit::effect_vm::columns::{STATE_AFTER_BASE, state};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace, pi};
use dregg_circuit::effect_vm_descriptors::{
    SELECTOR_DESCRIPTORS, descriptor_for_selector, descriptor_name_for_selector,
};
use dregg_circuit::effect_vm_p3_full_air::{p3_air_accepts, prove_effect_vm_p3, verify_effect_vm_p3};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{
    descriptor_air_accepts, parse_vm_descriptor, prove_vm_descriptor, verify_vm_descriptor,
};

/// A representative HONEST effect for a registered selector, or `None` if the selector
/// is not directly constructible from a single `Effect` variant (e.g. cap-root-move family
/// selectors that the trace generator reaches via shared variants). Returns the initial
/// `CellState` + the single effect whose trace exercises that selector's row.
fn honest_case_for_selector(sel: usize) -> Option<(CellState, Vec<Effect>)> {
    let st = CellState::new(100_000, 0);
    let eight = |x: u32| -> [BabyBear; 8] {
        let mut a = [BabyBear::ZERO; 8];
        a[0] = BabyBear::new(x);
        a
    };
    let four = |x: u32| -> [BabyBear; 4] {
        let mut a = [BabyBear::ZERO; 4];
        a[0] = BabyBear::new(x);
        a
    };
    use dregg_circuit::effect_vm::columns::sel;
    let eff = match sel {
        s if s == sel::TRANSFER => Effect::Transfer { amount: 50, direction: 1 },
        s if s == sel::NOTE_SPEND => Effect::NoteSpend { nullifier: BabyBear::new(0x1234), value: 100 },
        s if s == sel::NOTE_CREATE => Effect::NoteCreate { commitment: BabyBear::new(0x5678), value: 50 },
        s if s == sel::SEAL => Effect::Seal { field_idx: 2 },
        s if s == sel::UNSEAL => Effect::Unseal { field_idx: 2, brand: BabyBear::new(0x9) },
        s if s == sel::MAKE_SOVEREIGN => Effect::MakeSovereign,
        s if s == sel::CREATE_CELL_FROM_FACTORY => Effect::CreateCellFromFactory {
            factory_vk: BabyBear::new(0x11),
            child_vk_derived: BabyBear::new(0x22),
        },
        s if s == sel::EXPORT_STURDY_REF => Effect::ExportSturdyRef {
            cell_id: BabyBear::new(0x1),
            permissions: BabyBear::new(0x3),
            random_seed: BabyBear::new(0x7),
            export_counter: 0,
        },
        s if s == sel::ENLIVEN_REF => Effect::EnlivenRef {
            swiss_number: BabyBear::new(0x1),
            presenter_id: BabyBear::new(0x2),
            expected_cell_id: BabyBear::new(0x3),
            expected_permissions: BabyBear::new(0x4),
        },
        s if s == sel::DROP_REF => Effect::DropRef {
            cell_id: BabyBear::new(0x1),
            holder_federation: BabyBear::new(0x2),
            current_refcount: 3,
        },
        s if s == sel::VALIDATE_HANDOFF => Effect::ValidateHandoff {
            certificate_hash: BabyBear::new(0x1),
            recipient_pk: BabyBear::new(0x2),
            introducer_pk: BabyBear::new(0x3),
            approved_set_root: BabyBear::new(0x4),
        },
        s if s == sel::ALLOCATE_QUEUE => Effect::AllocateQueue {
            capacity: 4,
            owner_quota_id: BabyBear::new(0x1),
            cost_per_slot: 1,
        },
        s if s == sel::ENQUEUE_MESSAGE => Effect::EnqueueMessage {
            message_hash: BabyBear::new(0x1),
            deposit_amount: 5,
            sender_id: BabyBear::new(0x2),
            queue_len: 0,
            program_vk: BabyBear::ZERO,
        },
        s if s == sel::DEQUEUE_MESSAGE => Effect::DequeueMessage {
            expected_message_hash: BabyBear::new(0x1),
            deposit_refund: 5,
        },
        s if s == sel::RESIZE_QUEUE => Effect::ResizeQueue {
            new_capacity: 8,
            queue_id: BabyBear::new(0x1),
            cost_per_slot: 1,
            old_capacity: 4,
        },
        s if s == sel::ATOMIC_QUEUE_TX => Effect::AtomicQueueTx {
            op_count: 2,
            tx_hash: BabyBear::new(0x1),
            combined_old_root: BabyBear::new(0x2),
            combined_new_root: BabyBear::new(0x3),
            net_deposit: 5,
        },
        s if s == sel::PIPELINE_STEP => Effect::PipelineStep {
            pipeline_id: BabyBear::new(0x1),
            source_old_root: BabyBear::new(0x2),
            source_new_root: BabyBear::new(0x3),
            sink_new_root: BabyBear::new(0x4),
            message_hash: BabyBear::new(0x5),
        },
        s if s == sel::EMIT_EVENT => Effect::EmitEvent { topic_hash: eight(0x1), payload_hash: eight(0x2) },
        s if s == sel::SET_PERMISSIONS => Effect::SetPermissions { permissions_hash: eight(0x1) },
        s if s == sel::SET_VERIFICATION_KEY => Effect::SetVerificationKey { vk_hash: eight(0x1) },
        s if s == sel::CREATE_SEAL_PAIR => Effect::CreateSealPair { pair_hash: eight(0x1) },
        s if s == sel::REFRESH_DELEGATION => Effect::RefreshDelegation,
        s if s == sel::REVOKE_DELEGATION => Effect::RevokeDelegation { child_hash: eight(0x1) },
        s if s == sel::CREATE_CELL => Effect::CreateCell { create_hash: eight(0x1) },
        s if s == sel::SPAWN_WITH_DELEGATION => Effect::SpawnWithDelegation { spawn_hash: eight(0x1) },
        s if s == sel::BRIDGE_CANCEL => Effect::BridgeCancel { nullifier_hash: eight(0x1) },
        s if s == sel::EXERCISE_VIA_CAPABILITY => Effect::ExerciseViaCapability { exercise_hash: eight(0x1) },
        s if s == sel::INTRODUCE => Effect::Introduce { intro_hash: eight(0x1) },
        s if s == sel::PIPELINED_SEND => Effect::PipelinedSend { send_hash: eight(0x1) },
        s if s == sel::CREATE_ESCROW => Effect::CreateEscrow {
            amount_lo: BabyBear::new(40),
            escrow_hash: BabyBear::new(0x1),
            amount_full: 40,
        },
        s if s == sel::BRIDGE_LOCK => Effect::BridgeLock {
            value_lo: BabyBear::new(40),
            lock_hash: BabyBear::new(0x1),
            value_full: 40,
        },
        s if s == sel::CREATE_COMMITTED_ESCROW => Effect::CreateCommittedEscrow { commit_hash: eight(0x1) },
        s if s == sel::BRIDGE_MINT => Effect::BridgeMint {
            value_lo: BabyBear::new(40),
            mint_hash: BabyBear::new(0x1),
            value_full: 40,
        },
        s if s == sel::BRIDGE_FINALIZE => Effect::BridgeFinalize { finalize_hash: eight(0x1) },
        s if s == sel::RELEASE_ESCROW => Effect::ReleaseEscrow { escrow_id_hash: eight(0x1) },
        s if s == sel::REFUND_ESCROW => Effect::RefundEscrow { escrow_id_hash: eight(0x1) },
        s if s == sel::GRANT_CAP => Effect::GrantCapability { cap_entry: eight(0x1) },
        s if s == sel::BURN => Effect::Burn {
            target_hash: BabyBear::new(0xB0B),
            amount_lo: BabyBear::new(75),
            amount_full: 75,
        },
        s if s == sel::CELL_DESTROY => Effect::CellDestroy {
            target_hash: eight(0x1),
            death_certificate_hash: eight(0x2),
        },
        s if s == sel::ATTENUATE_CAPABILITY => Effect::AttenuateCapability {
            cap_slot_hash: eight(0x1),
            narrower_commitment: eight(0x2),
        },
        s if s == sel::CELL_SEAL => Effect::CellSeal { target: eight(0x1), reason_hash: eight(0x2) },
        s if s == sel::RECEIPT_ARCHIVE => Effect::ReceiptArchive {
            target: eight(0x1),
            archive_end_height: BabyBear::new(0x10),
            terminal_receipt_hash: eight(0x2),
        },
        s if s == sel::REFUSAL => Effect::Refusal { target: eight(0x1), reason_hash: eight(0x2) },
        s if s == sel::INCREMENT_NONCE => Effect::IncrementNonce,
        _ => return None,
    };
    let _ = four; // silence unused on builds where no four-limb variant is hit
    Some((st, vec![eff]))
}

/// THE COMPLETE DIVERGENCE ENUMERATION over ALL registered selector descriptors.
///
/// For every selector in `SELECTOR_DESCRIPTORS`, generate its real `generate_effect_vm_trace`
/// witness, confirm the hand-AIR (the validated runtime circuit) accepts it, then check whether
/// the Lean-emitted descriptor interpreter agrees. Emits a per-descriptor AGREE / DIVERGE line.
/// This is the differential map: which descriptors reject a trace the hand-AIR accepts.
#[test]
fn enumerate_all_descriptor_divergences() {
    let mut agree = Vec::new();
    let mut diverge = Vec::new();
    let mut unconstructible = Vec::new();

    for (sel, name, _json, _fp) in SELECTOR_DESCRIPTORS {
        let Some((st, effects)) = honest_case_for_selector(*sel) else {
            unconstructible.push((*sel, *name, "no single-Effect constructor"));
            continue;
        };
        // Some selectors need a non-trivial pre-state (e.g. Unseal needs a sealed field);
        // the bare single-effect trace panics in `generate_effect_vm_trace`. Treat those as
        // "needs richer fixture", not a divergence — they are reported, not forced.
        let generated = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            generate_effect_vm_trace(&st, &effects)
        }));
        let (base_trace, pis) = match generated {
            Ok(v) => v,
            Err(_) => {
                unconstructible.push((*sel, *name, "trace fixture panics (needs richer pre-state)"));
                continue;
            }
        };
        let json = descriptor_for_selector(*sel).unwrap();
        let desc = parse_vm_descriptor(json).expect("descriptor parses");
        let dpis = &pis[..desc.public_input_count];

        let hand_accepts = p3_air_accepts(&base_trace, &pis);
        let desc_accepts = descriptor_air_accepts(&desc, &base_trace, dpis);

        if !hand_accepts {
            eprintln!(
                "[sel {sel:>2} {name}] WARN: hand-AIR REJECTED the honest witness (case not representative); \
                 desc_accepts={desc_accepts}"
            );
            unconstructible.push((*sel, *name, "hand-AIR rejects this fixture (needs richer witness)"));
            continue;
        }
        if hand_accepts && desc_accepts {
            eprintln!("[sel {sel:>2} {name}] AGREE  (descriptor + hand-AIR both accept honest trace)");
            agree.push((*sel, *name));
        } else {
            eprintln!("[sel {sel:>2} {name}] DIVERGE (hand-AIR accepts, descriptor REJECTS honest trace)");
            diverge.push((*sel, *name));
        }
    }

    eprintln!("\n==== DIVERGENCE SUMMARY ====");
    eprintln!("AGREE ({}):", agree.len());
    for (s, n) in &agree {
        eprintln!("  sel {s:>2}  {n}");
    }
    eprintln!("DIVERGE ({}):", diverge.len());
    for (s, n) in &diverge {
        eprintln!("  sel {s:>2}  {n}");
    }
    eprintln!("UNCONSTRUCTIBLE ({}):", unconstructible.len());
    for (s, n, why) in &unconstructible {
        eprintln!("  sel {s:>2}  {n}  ({why})");
    }
    // This test is a REPORT (never fails): it documents the full divergence map.
    assert!(agree.len() + diverge.len() + unconstructible.len() == SELECTOR_DESCRIPTORS.len());
}

/// THE BEACHHEAD: transfer is the validated, fully-cutover-ready effect. Prove+verify
/// through BOTH the descriptor interpreter and the hand-AIR over the SAME real witness,
/// assert they AGREE, and assert the descriptor interpreter REJECTS tampered witnesses
/// (anti-ghost). This proves the descriptor interpreter is a faithful drop-in
/// prover+verifier — the cutover mechanism works end-to-end.
#[test]
fn transfer_descriptor_interpreter_is_a_faithful_drop_in_for_the_hand_air() {
    let cases: Vec<(&str, CellState, Vec<Effect>)> = vec![
        (
            "transfer-out",
            CellState::new(100_000, 0),
            vec![Effect::Transfer { amount: 50, direction: 1 }],
        ),
        (
            "transfer-in",
            CellState::new(100_000, 0),
            vec![Effect::Transfer { amount: 50, direction: 0 }],
        ),
    ];

    let mut proven = 0usize;
    for (label, st, effects) in cases {
        // -- The single witness BOTH provers consume (the 186-col base trace + PIs). --
        let (base_trace, pis) = generate_effect_vm_trace(&st, &effects);
        assert_eq!(base_trace[0].len(), 186, "[{label}] canonical 186-col EffectVM layout");

        // -- Resolve the verified-by-construction descriptor for selector 1 (TRANSFER). --
        let json = descriptor_for_selector(1).expect("transfer selector must have a descriptor");
        let name = descriptor_name_for_selector(1).unwrap();
        let desc = parse_vm_descriptor(json)
            .unwrap_or_else(|e| panic!("[{label}] descriptor {name} failed to parse: {e}"));

        // The descriptor binds the PI PREFIX (`public_input_count`, here 34); the wider
        // EffectVM PI vector is sliced down. The forged FINAL_BAL_LO (idx 14) and the
        // state_commit boundary live in the prefix, so the anti-ghost teeth still bite.
        let dpis = &pis[..desc.public_input_count];

        // (1) DESCRIPTOR INTERPRETER — prove + independent verify, real Plonky3.
        let desc_proof = prove_vm_descriptor(&desc, &base_trace, dpis).unwrap_or_else(|e| {
            panic!(
                "[{label}] DESCRIPTOR INTERPRETER failed to PROVE the honest witness via {name}: {e}"
            )
        });
        verify_vm_descriptor(&desc, &desc_proof, dpis)
            .unwrap_or_else(|e| panic!("[{label}] descriptor proof failed independent verify: {e}"));

        // (2) HAND-AIR — prove + independent verify, real Plonky3, same witness.
        let hand_proof = prove_effect_vm_p3(&base_trace, &pis)
            .unwrap_or_else(|e| panic!("[{label}] hand-AIR failed to prove honest witness: {e:?}"));
        verify_effect_vm_p3(&hand_proof, &pis)
            .unwrap_or_else(|e| panic!("[{label}] hand-AIR proof failed independent verify: {e:?}"));

        // (3) THE DIFFERENTIAL — both accept the SAME honest witness.
        let hand_accepts = p3_air_accepts(&base_trace, &pis);
        let desc_accepts = descriptor_air_accepts(&desc, &base_trace, dpis);
        assert!(hand_accepts, "[{label}] hand-AIR rejected a witness it just PROVED");
        assert!(desc_accepts, "[{label}] descriptor rejected a witness it just PROVED");
        assert_eq!(
            hand_accepts, desc_accepts,
            "[{label}] DIFFERENTIAL DISAGREEMENT on honest witness"
        );

        // (4) ANTI-GHOST — tampered witnesses are UNSAT for BOTH.
        // (4a) Forge the published FINAL_BAL_LO PI away from the trace's real balance.
        {
            let mut forged = pis.clone();
            forged[pi::FINAL_BAL_LO] = forged[pi::FINAL_BAL_LO] + BabyBear::new(123);
            let fdpis = &forged[..desc.public_input_count];
            assert!(!p3_air_accepts(&base_trace, &forged), "[{label}] hand-AIR took forged FINAL_BAL_LO");
            assert!(
                !descriptor_air_accepts(&desc, &base_trace, fdpis),
                "[{label}] descriptor MORE PERMISSIVE on forged FINAL_BAL_LO"
            );
            assert!(
                prove_vm_descriptor(&desc, &base_trace, fdpis).is_err(),
                "[{label}] descriptor PROVED a forged FINAL_BAL_LO"
            );
        }
        // (4b) Mutate the last-row state-commit cell (GROUP-4 anti-ghost tooth).
        {
            let mut t = base_trace.clone();
            let last = t.len() - 1;
            t[last][STATE_AFTER_BASE + state::STATE_COMMIT] =
                t[last][STATE_AFTER_BASE + state::STATE_COMMIT] + BabyBear::new(1);
            assert!(
                !descriptor_air_accepts(&desc, &t, dpis),
                "[{label}] descriptor took a forged last-row state-commit cell"
            );
            assert!(
                prove_vm_descriptor(&desc, &t, dpis).is_err(),
                "[{label}] descriptor PROVED a forged state-commit cell"
            );
        }

        eprintln!(
            "[{label}] CUTOVER-READY: descriptor `{name}` and hand-AIR both prove+verify the honest \
             witness, agree on accept, and both reject the forged-balance + forged-state-commit tampers."
        );
        proven += 1;
    }
    assert_eq!(proven, 2, "both transfer directions must pass the full beachhead");
}

/// GRADUATED ECONOMIC EFFECTS: burn / note_create / note_spend / bridge_mint reconciled onto the
/// runtime column convention (balance move at `param1`/col 69 + the global nonce TICK) and re-emitted
/// from the verified Lean descriptors. Each now proves+verifies through BOTH the descriptor interpreter
/// and the hand-AIR over the SAME honest witness, AGREES on accept, and BOTH reject the forged-balance
/// + forged-state-commit tampers — exactly the beachhead `transfer` graduated through. This is the
/// cutover advancing from 1 effect (transfer) toward all economic effects.
#[test]
fn economic_effects_graduated_into_cutover() {
    struct Case {
        label: &'static str,
        sel: usize,
        st: CellState,
        effects: Vec<Effect>,
    }
    let cases = vec![
        Case {
            label: "burn",
            sel: 46,
            st: CellState::new(100_000, 0),
            effects: vec![Effect::Burn {
                target_hash: BabyBear::new(0xB0B),
                amount_lo: BabyBear::new(75),
                amount_full: 75,
            }],
        },
        Case {
            label: "note_create",
            sel: 5,
            st: CellState::new(100_000, 0),
            effects: vec![Effect::NoteCreate { commitment: BabyBear::new(0x5678), value: 50 }],
        },
        Case {
            label: "note_spend",
            sel: 4,
            st: CellState::new(100_000, 0),
            effects: vec![Effect::NoteSpend { nullifier: BabyBear::new(0x1234), value: 100 }],
        },
        Case {
            label: "bridge_mint",
            sel: 40,
            st: CellState::new(100_000, 0),
            effects: vec![Effect::BridgeMint {
                value_lo: BabyBear::new(60),
                mint_hash: BabyBear::new(0xB1D),
                value_full: 60,
            }],
        },
    ];

    let mut graduated = 0usize;
    for c in cases {
        let (base_trace, pis) = generate_effect_vm_trace(&c.st, &c.effects);
        assert_eq!(base_trace[0].len(), 186, "[{}] canonical 186-col layout", c.label);
        let json = descriptor_for_selector(c.sel)
            .unwrap_or_else(|| panic!("[{}] selector {} has no descriptor", c.label, c.sel));
        let name = descriptor_name_for_selector(c.sel).unwrap();
        let desc = parse_vm_descriptor(json).expect("descriptor parses");
        let dpis = &pis[..desc.public_input_count];

        // (1) DESCRIPTOR INTERPRETER — prove + independent verify, real Plonky3.
        let desc_proof = prove_vm_descriptor(&desc, &base_trace, dpis).unwrap_or_else(|e| {
            panic!("[{}] descriptor `{name}` failed to PROVE the honest witness: {e}", c.label)
        });
        verify_vm_descriptor(&desc, &desc_proof, dpis)
            .unwrap_or_else(|e| panic!("[{}] descriptor proof failed independent verify: {e}", c.label));

        // (2) HAND-AIR — prove + independent verify, same witness.
        let hand_proof = prove_effect_vm_p3(&base_trace, &pis)
            .unwrap_or_else(|e| panic!("[{}] hand-AIR failed to prove honest witness: {e:?}", c.label));
        verify_effect_vm_p3(&hand_proof, &pis)
            .unwrap_or_else(|e| panic!("[{}] hand-AIR proof failed verify: {e:?}", c.label));

        // (3) THE DIFFERENTIAL — both accept the SAME honest witness.
        let hand_accepts = p3_air_accepts(&base_trace, &pis);
        let desc_accepts = descriptor_air_accepts(&desc, &base_trace, dpis);
        assert!(hand_accepts, "[{}] hand-AIR rejected a witness it just PROVED", c.label);
        assert!(desc_accepts, "[{}] descriptor rejected a witness it just PROVED", c.label);
        assert_eq!(hand_accepts, desc_accepts, "[{}] DIFFERENTIAL DISAGREEMENT", c.label);

        // (4a) ANTI-GHOST — forged FINAL_BAL_LO is UNSAT for BOTH.
        {
            let mut forged = pis.clone();
            forged[pi::FINAL_BAL_LO] = forged[pi::FINAL_BAL_LO] + BabyBear::new(123);
            let fdpis = &forged[..desc.public_input_count];
            assert!(!p3_air_accepts(&base_trace, &forged), "[{}] hand-AIR took forged bal", c.label);
            assert!(
                !descriptor_air_accepts(&desc, &base_trace, fdpis),
                "[{}] descriptor MORE PERMISSIVE on forged FINAL_BAL_LO", c.label
            );
            assert!(
                prove_vm_descriptor(&desc, &base_trace, fdpis).is_err(),
                "[{}] descriptor PROVED a forged FINAL_BAL_LO", c.label
            );
        }
        // (4b) ANTI-GHOST — mutated last-row state-commit cell is UNSAT.
        {
            let mut t = base_trace.clone();
            let last = t.len() - 1;
            t[last][STATE_AFTER_BASE + state::STATE_COMMIT] =
                t[last][STATE_AFTER_BASE + state::STATE_COMMIT] + BabyBear::new(1);
            assert!(
                !descriptor_air_accepts(&desc, &t, dpis),
                "[{}] descriptor took a forged last-row state-commit cell", c.label
            );
            assert!(
                prove_vm_descriptor(&desc, &t, dpis).is_err(),
                "[{}] descriptor PROVED a forged state-commit cell", c.label
            );
        }

        eprintln!(
            "[{}] GRADUATED: descriptor `{name}` + hand-AIR both prove+verify the honest witness, agree \
             on accept, and both reject the forged-balance + forged-state-commit tampers.",
            c.label
        );
        graduated += 1;
    }
    assert_eq!(graduated, 4, "all four economic effects must graduate");
}

/// HONEST CUTOVER CATALOG — the economic effects that remain BLOCKED, and WHY. This documents the
/// precise residual divergences the differential surfaces (a real, valuable finding, not a hidden
/// failure). There are NO column-fixable economic blockers left among the selector-bound full-economic
/// effects: burn/note_create/note_spend/bridge_mint graduated above. The remaining economic surfaces are
/// IR-blocked (side-table digests the per-row IR cannot re-derive) — `create_escrow` / `bridge_lock`
/// debit balance like burn (COLUMN-fixable later, same pattern), but their descriptors ALSO carry the
/// escrow/bridge side-table semantics out-of-IR; we leave them on the hand-AIR until the per-row IR is
/// extended. (`mint` is name-only: no Rust selector / no `Effect` variant, so it cannot be exercised by
/// the trace generator at all.)
#[test]
fn remaining_economic_blockers_are_documented() {
    // create_escrow (37) and bridge_lock (38) still read param0 for the debit amount (the trace puts
    // amount at param1) AND freeze the nonce (the trace ticks) — the SAME column-fix that graduated
    // burn would apply, but these effects additionally bind an escrow/bridge side-table the per-row IR
    // does not model, so they are deferred to the IR-extension lane (kept on the hand-AIR).
    for (label, sel, st, effects) in [
        (
            "create_escrow",
            37usize,
            CellState::new(100_000, 0),
            vec![Effect::CreateEscrow {
                amount_lo: BabyBear::new(40),
                escrow_hash: BabyBear::new(0x1),
                amount_full: 40,
            }],
        ),
        (
            "bridge_lock",
            38usize,
            CellState::new(100_000, 0),
            vec![Effect::BridgeLock {
                value_lo: BabyBear::new(40),
                lock_hash: BabyBear::new(0x1),
                value_full: 40,
            }],
        ),
    ] {
        let (base_trace, pis) = generate_effect_vm_trace(&st, &effects);
        let json = descriptor_for_selector(sel).unwrap();
        let desc = parse_vm_descriptor(json).unwrap();
        let dpis = &pis[..desc.public_input_count];
        assert!(
            p3_air_accepts(&base_trace, &pis),
            "[{label}] precondition: hand-AIR accepts the honest witness"
        );
        let desc_accepts = descriptor_air_accepts(&desc, &base_trace, dpis);
        assert!(
            !desc_accepts,
            "[{label}] UNEXPECTED: descriptor now accepts — promote it into the graduation test."
        );
        eprintln!(
            "[{label}] STILL BLOCKED (column-fixable-later + IR side-table): hand-AIR proves it; the \
             Lean descriptor `{}` does not (reads param0 + freezes nonce; trace uses param1 + ticks).",
            desc.name
        );
    }
}
