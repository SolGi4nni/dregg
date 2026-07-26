//! # THE SOVEREIGN PRODUCER FAILS CLOSED on a verb the after-cell weld cannot project.
//!
//! `prove_sovereign_turn_rotated` derives the AFTER block from
//! `dregg_turn::rotation_witness::apply_effect_to_cell`, and that AFTER block IS the sovereign
//! cell's next state: it feeds `rw::produce` → the 8-felt wide commit → the turn's
//! `execution_proof_new_commitment`, and `executor::execute`'s PHASE 3 does **zero state
//! manipulation** for a proof-carrying turn — it verifies the proof and writes that one commitment.
//!
//! Nothing downstream re-derives the transition for a non-record-pin lead:
//! `verify_and_commit_proof_rotated` anchors the after-commit PIs to
//! `bytes32_to_felt8(turn.execution_proof_new_commitment)` — the prover's own claim — and its
//! off-cell record-pin re-derivation is `Anchor::None` for every lead outside the eight-variant
//! record-pin family. So for a verb whose executor apply leg writes a committed field of the acting
//! cell that the weld does NOT project, the producer would mint a proof that verifies and attests
//! "these effects happened AND the state did not change."
//!
//! The producer now refuses those turns instead, keyed off the ONE wildcard-free list
//! (`rotation_witness::weld_coverage`, grounded against the live weld by
//! `turn/tests/sovereign_after_cell_weld_ledger.rs`). Refusing is the response that neither binds a
//! false transition nor moves the proof bytes of a turn that already committed.
//!
//! These tests need no STARK: the refusal happens before any trace generation.

#![cfg(feature = "prover")]

use dregg_cell::commitment::{V9RotationContext, compute_canonical_state_commitment_v9_8};
use dregg_cell::{Cell, CellId, CellMode, Ledger};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::rotation_witness as rw;
use dregg_turn::{ComputronCosts, Effect, TurnExecutor, TurnResult};

/// A sovereign cell whose local state the cipherclerk holds — all the refusal tests need, since the
/// coverage gate fires at step 1a, before any ledger or trace is touched. (The ledger-carrying
/// variant below is for the tests that go all the way through the executor.)
fn setup(balance: i64) -> (AgentCipherclerk, CellId, CellId) {
    let mut cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(b"weld-refusal-domain").as_bytes();

    let mut cell = Cell::with_balance(pub_key, token_id, balance);
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();
    cclerk.store_sovereign_state(cell);

    let other = Cell::with_balance([0x4Du8; 32], token_id, 0).id();
    (cclerk, cell_id, other)
}

/// The same cell, plus the LEDGER view the executor verifies against (a registered sovereign
/// commitment + a destination cell) — for the end-to-end chain test below.
fn setup_with_ledger(balance: i64) -> (AgentCipherclerk, CellId, CellId, Ledger) {
    let mut cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(b"weld-chain-domain").as_bytes();

    let mut cell = Cell::with_balance(pub_key, token_id, balance);
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();

    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(cell.clone());
    let ctx = V9RotationContext {
        cells_root: rw::cells_root(&ctx_ledger),
        nullifier_root: dregg_circuit::heap_root::empty_heap_root_8(),
        commitments_root: dregg_circuit::heap_root::empty_heap_root_8(),
        revoked_root: dregg_circuit::heap_root::empty_heap_root_8(),
        iroot: rw::iroot(&[]),
        material: Default::default(),
    };
    let commitment = compute_canonical_state_commitment_v9_8(&cell, &ctx);
    cclerk.store_sovereign_state(cell.clone());

    let mut ledger = Ledger::new();
    ledger.register_sovereign_cell(cell_id, commitment).unwrap();
    let _ = ledger.insert_cell(cell);

    let dest = Cell::with_balance([0x4Du8; 32], token_id, 0);
    let dest_id = dest.id();
    let _ = ledger.insert_cell(dest);

    (cclerk, cell_id, dest_id, ledger)
}

/// **A self-burn is REFUSED.** `apply_burn` debits `state.balance` (rotated limbs 1 lo / 3 hi) on the
/// burned cell, and the deployed projector already mints a DEBITING
/// `VmEffect::Transfer { direction: 1 }` row for it — so the VM row and the AFTER block disagreed
/// about the balance, with nothing forcing them to agree. The refusal must NAME the verb and the
/// field, not fail vaguely.
#[test]
fn a_self_burn_is_refused_and_the_refusal_names_the_field() {
    let (mut cclerk, cell_id, _other) = setup(100_000);
    let err = cclerk
        .execute_sovereign_turn_with_proof(
            &cell_id,
            vec![Effect::Burn {
                target: cell_id,
                slot: 0,
                amount: 11,
            }],
            0,
            0,
        )
        .expect_err("a self-burn must be refused, not proven against a frozen balance");
    let s = format!("{err}");
    assert!(
        s.contains("Burn") && s.contains("balance"),
        "the refusal must name the verb and the field it cannot project: {s}"
    );
    assert!(
        s.contains("did not happen") || s.contains("byte-identical"),
        "and must say WHY refusing is the right answer: {s}"
    );
}

/// **A cap-root mover is REFUSED.** `capabilities.revoke(slot)` moves
/// `compute_canonical_capability_root_8` (limb 25 ‖ 52..=58); the weld does not project it.
#[test]
fn a_capability_revoke_is_refused() {
    let (mut cclerk, cell_id, _other) = setup(100_000);
    let err = cclerk
        .execute_sovereign_turn_with_proof(
            &cell_id,
            vec![Effect::RevokeCapability {
                cell: cell_id,
                slot: 0,
            }],
            0,
            0,
        )
        .expect_err("a cap-root mover must be refused");
    assert!(
        format!("{err}").contains("RevokeCapability"),
        "the refusal must name the verb: {err}"
    );
}

/// **The refusal is POSITIONAL, not lead-only.** A mover in the TAIL of a turn poisons it too — the
/// pre-flip producer applied its eleven-arm match over EVERY effect, so a tail mover left the same
/// frozen limb. Refusing only on the lead would leave the hole open for `[Transfer, Burn]`.
#[test]
fn a_mover_in_the_tail_refuses_the_whole_turn() {
    let (mut cclerk, cell_id, other) = setup(100_000);
    let err = cclerk
        .execute_sovereign_turn_with_proof(
            &cell_id,
            vec![
                Effect::Transfer {
                    from: cell_id,
                    to: other,
                    amount: 1,
                },
                Effect::Burn {
                    target: cell_id,
                    slot: 0,
                    amount: 11,
                },
            ],
            0,
            0,
        )
        .expect_err("a tail mover must refuse the whole turn");
    assert!(
        format!("{err}").contains("Burn"),
        "the refusal must name the TAIL verb: {err}"
    );
}

/// **THE CHAIN-PATH BINDING TEST (is the field write bound at all?).**
/// `prove_sovereign_cohort_chain` builds its `full_after_cell` from the weld alone (plus, until this
/// commit, a DUPLICATED hand-written `Transfer`), and the weld had no `SetField` arm. The question
/// this settles EMPIRICALLY — rather than by reasoning about which limbs the wide generator
/// overrides from the v1 sub-trace — is whether the committed NEW commitment of a heterogeneous
/// `[Transfer, SetField]` turn actually DEPENDS on the value written.
///
/// Two otherwise-identical turns writing DIFFERENT values must commit DIFFERENT commitments. If they
/// commit the same one, the value reaches no bound column and a light client cannot tell the two
/// turns apart from the state they published — which is the wound, one layer deeper than the weld.
///
/// This also pins the balance debiting EXACTLY once: a surviving duplicate hand `Transfer` arm beside
/// the new weld arm would debit 200 for a 100-transfer, and the chain anchors would not reconcile.
#[test]
fn a_two_cohort_turns_committed_commitment_depends_on_the_field_value() {
    fn run(value: u64) -> [u8; 32] {
        let (mut cclerk, cell_id, dest_id, mut ledger) = setup_with_ledger(1000);
        let effects = vec![
            Effect::Transfer {
                from: cell_id,
                to: dest_id,
                amount: 100,
            },
            Effect::SetField {
                cell: cell_id,
                index: 3,
                value: dregg_cell::field_from_u64(value),
            },
        ];
        let turn = cclerk
            .execute_sovereign_turn_with_proof(&cell_id, effects, 0, 0)
            .expect("a 2-cohort turn with a field write should prove as a chain");
        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!("the chained 2-cohort turn must COMMIT, got {other:?}"),
        }
        *ledger
            .get_sovereign_commitment(&cell_id)
            .expect("the sovereign commitment advanced")
    }

    assert_ne!(
        run(0x5E70),
        run(0x0BAD),
        "two heterogeneous turns writing DIFFERENT field values must commit DIFFERENT sovereign \
         commitments — otherwise the value is bound nowhere the committed state can see, and the \
         published transition does not distinguish them"
    );
}

/// **THE INVISIBLE EFFECT — the sharpest reachable case.** `SetProgram` is one of the five verbs the
/// deployed projector mints NO VM row for, so a LONE `SetProgram` turn projects to `[NoOp]` and fails
/// closed at descriptor resolution. But in a MIXED turn the projection simply drops it:
/// `[SetPermissions, SetProgram]` projects to a single `[SetPermissions]` cohort, proves as a
/// single-leg turn, and commits — while `apply_set_program` writes `cell.program`, which
/// `compute_authority_digest_8` folds (limbs 12..=18, 24). So the effect was in the turn body and in
/// `effects_hash`, invisible to the row set, and absent from the after-cell: a proof attesting a
/// permissions change while silently carrying an unattested program swap.
///
/// The coverage gate refuses the whole turn, naming `SetProgram`.
#[test]
fn a_dropped_effect_in_a_mixed_turn_refuses_rather_than_proving_around_it() {
    let (mut cclerk, cell_id, _other) = setup(100_000);
    let err = cclerk
        .execute_sovereign_turn_with_proof(
            &cell_id,
            vec![
                Effect::SetPermissions {
                    cell: cell_id,
                    new_permissions: dregg_cell::Permissions::default(),
                },
                Effect::SetProgram {
                    cell: cell_id,
                    program: dregg_cell::CellProgram::default(),
                },
            ],
            0,
            0,
        )
        .expect_err(
            "a turn carrying an effect the projector drops AND the weld cannot project must be \
             refused, not proven around",
        );
    let s = format!("{err}");
    assert!(
        s.contains("SetProgram") && s.contains("program"),
        "the refusal must name the dropped verb and the field: {s}"
    );
}

/// **The gate does not over-refuse.** A burn aimed at a DIFFERENT cell writes nothing on the acting
/// cell, so the weld's no-op is the correct projection and the turn must NOT be refused by this gate.
/// (It may still fail further down the wide route; what matters here is that it gets past step 1a —
/// an over-broad per-VERB gate would have killed every witnessing turn.)
#[test]
fn a_burn_aimed_elsewhere_is_not_refused_by_the_coverage_gate() {
    let (mut cclerk, cell_id, other) = setup(100_000);
    let outcome = cclerk.execute_sovereign_turn_with_proof(
        &cell_id,
        vec![Effect::Burn {
            target: other,
            slot: 0,
            amount: 11,
        }],
        0,
        0,
    );
    if let Err(e) = &outcome {
        let s = format!("{e}");
        assert!(
            !s.contains("refuses this turn"),
            "the coverage gate must not refuse a burn aimed at another cell: {s}"
        );
    }
}

/// **The weld carries BOTH writes into the producer's own advanced state** — the state the NEXT
/// turn's OLD_COMMIT is derived from, so a lost write here desynchronises the cell from the ledger on
/// the following turn. Split from the commitment discriminator above so each test carries one claim:
/// this one is about the SDK's local `sovereign_cells`, that one about what the executor committed.
#[test]
fn the_chained_producer_advances_its_local_state_with_both_writes() {
    let (mut cclerk, cell_id, dest_id, _ledger) = setup_with_ledger(1000);
    let effects = vec![
        Effect::Transfer {
            from: cell_id,
            to: dest_id,
            amount: 100,
        },
        Effect::SetField {
            cell: cell_id,
            index: 3,
            value: dregg_cell::field_from_u64(0x5E70),
        },
    ];
    let _turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 0, 0)
        .expect("a 2-cohort turn with a field write should prove as a chain");
    let advanced = cclerk
        .sovereign_state(&cell_id)
        .expect("advanced sovereign state")
        .clone();
    assert_eq!(
        advanced.state.balance(),
        900,
        "the transfer debits EXACTLY once — a surviving duplicate hand `Transfer` arm beside the new \
         weld arm would debit 200 for a 100-transfer"
    );
    assert_eq!(
        advanced.state.fields[3],
        dregg_cell::field_from_u64(0x5E70),
        "and the weld carries the field write. Before it absorbed this arm the chained producer's \
         `full_after_cell` never saw it, so the SDK advanced to a state with field[3] still zero"
    );
}
