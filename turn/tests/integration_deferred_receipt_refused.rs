//! A DEFERRED-WITNESS receipt must be REFUSED by the verifiers.
//!
//! `WitnessMode::Symbolic` commits a turn while stamping
//! [`dregg_turn::collapse::DEFERRED_STATE_HASH`] (all-zeros) into
//! `pre_state_hash` / `post_state_hash`. Such a receipt is **validly signed** —
//! the executor signs `receipt_hash()`, which includes the sentinel — so every
//! signature check passes. It carries NO commitment to any state, so a verifier
//! that accepts it has verified nothing about the state it purports to prove,
//! while returning `Ok(())`.
//!
//! These tests pin that the module-level default is REFUSAL, and that the
//! refusal is about the *deferred witness* and nothing else: the same receipts
//! pass every other check (structure, chain link, executor signature) under the
//! explicit `*_allowing_deferred` opt-ins.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    VerifyError,
    collapse::{WitnessMode, is_deferred},
    turn::{Turn, TurnReceipt, TurnResult},
    verify::{
        verify_receipt_chain, verify_receipt_chain_head, verify_receipt_chain_strict,
        verify_receipt_extends, verify_receipt_signature_with_keys,
    },
};

// ---------------------------------------------------------------------------
// Helpers — the `integration_symbolic_collapse.rs` idiom for producing a real
// symbolic receipt (NOT a hand-rolled struct literal: the point is that the
// EXECUTOR emits this shape).
// ---------------------------------------------------------------------------

const EXECUTOR_SEED: [u8; 32] = [0x42u8; 32];

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn bare_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn drive(exec: &TurnExecutor, ledger: &mut Ledger, mut turn: Turn) -> TurnReceipt {
    turn.previous_receipt_hash = exec.get_last_receipt_hash(&turn.agent);
    match exec.execute(&turn, ledger) {
        TurnResult::Committed { receipt, .. } => {
            exec.set_last_receipt_hash(receipt.agent, receipt.receipt_hash());
            receipt
        }
        other => panic!("expected commit, got {other:?}"),
    }
}

/// A 2-receipt, single-agent, executor-SIGNED chain produced in `mode`.
/// Returns the chain and the executor's public key.
fn signed_chain(mode: WitnessMode) -> (Vec<TurnReceipt>, [u8; 32]) {
    let mut ledger = Ledger::new();
    let alice = make_open_cell(0x01, 1_000);
    let bob = make_open_cell(0x02, 0);
    let (a, b) = (alice.id(), bob.id());
    ledger.insert_cell(alice).unwrap();
    ledger.insert_cell(bob).unwrap();

    let exec = TurnExecutor::new(ComputronCosts::zero()).with_executor_signing_key(EXECUTOR_SEED);
    exec.set_witness_mode(mode);

    let mut chain = Vec::new();
    for (nonce, amount) in [(0u64, 250u64), (1, 100)] {
        chain.push(drive(
            &exec,
            &mut ledger,
            bare_turn(
                a,
                nonce,
                vec![Effect::Transfer {
                    from: a,
                    to: b,
                    amount,
                }],
            ),
        ));
    }

    let pk = ed25519_dalek::SigningKey::from_bytes(&EXECUTOR_SEED)
        .verifying_key()
        .to_bytes();
    (chain, pk)
}

// ---------------------------------------------------------------------------
// THE GATE
// ---------------------------------------------------------------------------

/// **The deferred-receipt forgery.** A symbolic-mode receipt commits to NO
/// state (all-zero sentinel), yet it is a genuine, executor-signed receipt: the
/// signature covers the sentinel, so it verifies. Before this gate, every
/// verifier in `turn::verify` returned `Ok(())` on it — a chain proving nothing
/// about state passed a state-proof verifier.
#[test]
fn a_validly_signed_deferred_receipt_is_refused_by_every_chain_verifier() {
    // ── HONEST POLE FIRST. The same turns under Full mode must verify under
    // every verifier, or the refusals below would be indistinguishable from a
    // verifier that refuses everything.
    let (full_chain, pk) = signed_chain(WitnessMode::Full);
    assert!(
        full_chain.iter().all(|r| !is_deferred(r)),
        "honest pole: Full mode materializes real witnesses"
    );
    verify_receipt_chain(&full_chain).expect("honest pole: a Full chain verifies structurally");
    verify_receipt_chain_strict(&full_chain, &[pk])
        .expect("honest pole: a Full chain verifies strict");
    verify_receipt_chain_head(&full_chain).expect("honest pole: a Full chain yields a head");
    verify_receipt_extends(&full_chain[0], &full_chain[1])
        .expect("honest pole: a Full receipt extends its predecessor");

    // ── THE DEFERRED CHAIN. Same turns, same executor key, Symbolic mode.
    let (sym_chain, sym_pk) = signed_chain(WitnessMode::Symbolic);
    assert_eq!(pk, sym_pk, "same executor key in both modes");
    assert!(
        sym_chain.iter().all(is_deferred),
        "every symbolic receipt carries the deferred sentinel"
    );

    // The receipts ARE validly signed — this is what makes the hole dangerous.
    // The point-verifier (authorship only) accepts them, so nothing below can be
    // dismissed as "the signature was bad".
    for (i, r) in sym_chain.iter().enumerate() {
        verify_receipt_signature_with_keys(r, &[pk])
            .unwrap_or_else(|e| panic!("symbolic receipt {i} IS validly executor-signed: {e:?}"));
    }

    // ── THE REFUSALS, named at the exact index.
    let err = verify_receipt_chain(&sym_chain)
        .expect_err("a chain committing to NO state must not verify");
    assert!(
        matches!(err, VerifyError::DeferredWitness { index: 0 }),
        "expected DeferredWitness at index 0, got {err:?}"
    );

    let err = verify_receipt_chain_strict(&sym_chain, &[pk])
        .expect_err("a valid executor signature cannot authorize an absent witness");
    assert!(
        matches!(err, VerifyError::DeferredWitness { index: 0 }),
        "expected DeferredWitness at index 0, got {err:?}"
    );

    // The head-returning verifier is the sharpest case: it would otherwise hand
    // a caller `[0u8; 32]` AS the proved final state commitment.
    let err = verify_receipt_chain_head(&sym_chain)
        .expect_err("the deferred sentinel must never be returned as a proved head");
    assert!(
        matches!(err, VerifyError::DeferredWitness { .. }),
        "got {err:?}"
    );

    // ── `verify_receipt_extends` does NOT route through the chain verifier —
    // it is the online-append path and needs its own arm.
    let err = verify_receipt_extends(&sym_chain[0], &sym_chain[1])
        .expect_err("the online-append check must refuse a deferred receipt too");
    assert!(
        matches!(err, VerifyError::DeferredWitness { .. }),
        "got {err:?}"
    );
}

/// A single deferred receipt spliced into an otherwise-Full chain is refused at
/// ITS index — the refusal is per-receipt, not "the whole chain looked odd".
#[test]
fn one_deferred_receipt_poisons_the_chain_at_its_own_index() {
    let (full_chain, pk) = signed_chain(WitnessMode::Full);
    verify_receipt_chain_strict(&full_chain, &[pk]).expect("honest pole");

    // Splice the sentinel into the SECOND receipt and re-sign it, then re-link
    // nothing (index 1 is the last, so no successor hash to repair). The result
    // is a fully valid signed chain whose head commits to nothing.
    let mut spliced = full_chain.clone();
    spliced[1].pre_state_hash = dregg_turn::collapse::DEFERRED_STATE_HASH;
    spliced[1].post_state_hash = dregg_turn::collapse::DEFERRED_STATE_HASH;
    spliced[1].executor_signature = Some(dregg_turn::sign_receipt(&spliced[1], &EXECUTOR_SEED));

    // Structurally intact and correctly signed…
    verify_receipt_signature_with_keys(&spliced[1], &[pk])
        .expect("the spliced receipt is validly signed");

    // …and still refused, at index 1.
    let err = verify_receipt_chain_strict(&spliced, &[pk]).expect_err("must refuse");
    assert!(
        matches!(err, VerifyError::DeferredWitness { index: 1 }),
        "expected DeferredWitness at index 1, got {err:?}"
    );
    let err = verify_receipt_extends(&spliced[0], &spliced[1]).expect_err("must refuse");
    assert!(
        matches!(err, VerifyError::DeferredWitness { .. }),
        "got {err:?}"
    );
}

/// The LOCAL escape hatch: a caller that legitimately holds its own
/// un-collapsed symbolic receipts can still verify its own chain, by SAYING SO.
/// This also proves the refusal above is about the deferred witness and nothing
/// else — the identical bytes pass every structural and signature check here.
#[test]
fn the_local_opt_in_still_verifies_a_symbolic_chain() {
    use dregg_turn::verify::{
        verify_receipt_chain_allowing_deferred, verify_receipt_chain_strict_allowing_deferred,
        verify_receipt_extends_allowing_deferred,
    };

    let (sym_chain, pk) = signed_chain(WitnessMode::Symbolic);
    assert!(sym_chain.iter().all(is_deferred));

    verify_receipt_chain_allowing_deferred(&sym_chain)
        .expect("a local symbolic chain is structurally sound");
    verify_receipt_chain_strict_allowing_deferred(&sym_chain, &[pk])
        .expect("a local symbolic chain is correctly executor-signed");
    verify_receipt_extends_allowing_deferred(&sym_chain[0], &sym_chain[1])
        .expect("a local symbolic receipt extends its predecessor");

    // The opt-in relaxes ONLY the witness question. A broken link is still
    // broken with `allow_deferred` on.
    let mut broken = sym_chain.clone();
    broken[1].previous_receipt_hash = Some([0xDE; 32]);
    let err = verify_receipt_chain_allowing_deferred(&broken)
        .expect_err("allowing deferred must not relax causal continuity");
    assert!(
        matches!(err, VerifyError::HashChainBreak { index: 1, .. }),
        "got {err:?}"
    );
}
