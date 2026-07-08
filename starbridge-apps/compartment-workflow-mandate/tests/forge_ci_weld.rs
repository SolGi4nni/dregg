//! THE PAYOFF WELD — a CWM CI-workflow charter's SIGNED terminal receipt gates a
//! forge PR's required check, end-to-end (`docs/deos/DREGG-FORGE.md`, "THE ONE WELD").
//!
//! A CI pipeline IS a `compartment-workflow-mandate` charter: a step DAG
//! (review -> redact -> sign, standing in for fetch -> build -> test) whose each
//! `advance_step` is a `Signature`-cap-gated, `step_clearance_ok` clearance-checked,
//! `cwm_cell_program`-enforced verified turn. The forge (`dregg-doc`) side gates a
//! `PullRequest`'s merge on a `RequiredCheck::CommittedReceipt{turn_hash,
//! trusted_executor_keys}` — satisfied ONLY by that exact turn's COMMITTED,
//! executor-SIGNED `TurnReceipt`.
//!
//! The weld is exactly one signature domain (Route (ii), the grain HOST signs):
//! [`fire_advance_step_signed`] installs the host's executor signing seed on the
//! mandate cell's embedded executor, so the terminal `advance_step` commits a
//! `Finality::Final` + Ed25519-signed receipt over the canonical executor-signed
//! message. [`planned_advance_turn_hash`] is the deterministic pre-image so the forge
//! can NAME the terminal turn BEFORE it runs (the analogue of
//! `dregg_doc::ExecutorDrivenDoc::planned_turn_hash`). No trusted CI runner: the
//! proof IS the pass, and the runner cannot forge the signature.
//!
//! TWO POLES + wrong-key refusal:
//!   (i)  charter NOT at terminal (no witness, or a non-terminal step's receipt)
//!        -> `PullRequest::land` REFUSED with `CheckNotSatisfied` (nothing merged);
//!   (ii) charter driven to terminal -> the signed terminal receipt satisfies the
//!        check -> the PR LANDS (finalized merge turns).
//!   + the SAME terminal receipt against a WRONG host key is refused
//!     (`SignatureUnverified`).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, DeosApp, EmbeddedExecutor, field_from_u64,
};
use dregg_doc::{
    AtomId, Author, CheckRefusal, CheckWitness, ExecutorDrivenDoc, History, Op, Patch, PullRequest,
    PullRequestError, RequiredCheck,
};
use dregg_turn::{Finality, TurnReceipt, verify_receipt_signature_with_keys};

use starbridge_compartment_workflow_mandate::{
    STEP_CURSOR_SLOT, charter_clearance_root, fire_advance_step, fire_advance_step_signed,
    officer_label, planned_advance_turn_hash, seed_workflow, workflow_app,
};

/// The grain host's executor signing seed (the forge trust anchor). RFC-8032 test
/// vector seed; its derived verifying key is a forge repo-policy datum.
const HOST_SEED: [u8; 32] = [
    0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec, 0x2c, 0xc4,
    0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03, 0x1c, 0xae, 0x7f, 0x60,
];

/// A DIFFERENT host key — the wrong trust anchor. Derived through a throwaway
/// executor (no direct ed25519 dep needed; the executor owns the key derivation).
fn wrong_pubkey() -> [u8; 32] {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x99; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    executor.set_executor_signing_key([0x11u8; 32]);
    executor.executor_pubkey().expect("a foreign host pubkey")
}

/// A clean forge PR: base tombstones "one\n", head appends "three\n" — disjoint,
/// non-conflicting edits on a shared ancestor (its merge is "two\nthree\n").
fn clean_pr() -> PullRequest {
    let mut shared = History::new();
    let (s1, op1) = Patch::add(1, "one\n", AtomId::ROOT);
    let (s2, op2) = Patch::add(2, "two\n", s1);
    shared.commit(Patch::by(Author(0), [op1]));
    shared.commit(Patch::by(Author(0), [op2]));

    let mut base = shared.branch();
    base.commit(Patch::by(Author(1), [Op::Delete { id: s1 }]));
    let mut head = shared.branch();
    head.commit(Patch::by(Author(2), [Patch::add(3, "three\n", s2).1]));
    PullRequest::open(base, head)
}

/// A fresh CWM CI charter (terminal 3: review -> redact -> sign), the host executor
/// signing key installed, driven by the officer to ONE STEP from terminal (cursor
/// 2). Returns the app + SDK surface plus the last intermediate SIGNED receipt (the
/// 1 -> 2 advance) — a genuine, signed, but NON-terminal receipt.
fn charter_one_step_from_terminal(
    seed: u8,
) -> (AppCipherclerk, EmbeddedExecutor, DeosApp, TurnReceipt) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let app = workflow_app(&cclerk, &executor);
    // Charter terminal 3, cursor 0, the REAL clearance-graph root (so the officer's
    // advances are admitted by the executor's root-bound ClearanceDominates).
    seed_workflow(&executor, 42, 3, charter_clearance_root(), 5);
    // Route (ii): install the host executor signing seed BEFORE driving, so every
    // committed receipt (including the intermediate ones) is executor-signed.
    executor.set_executor_signing_key(HOST_SEED);
    // 0 -> 1
    fire_advance_step(
        &app,
        &AuthRequired::None,
        officer_label(),
        &cclerk,
        &executor,
    )
    .expect("intermediate CI step 0 -> 1 commits");
    // 1 -> 2 (the intermediate receipt we keep — signed, Final, but NOT the terminal turn).
    let intermediate = fire_advance_step(
        &app,
        &AuthRequired::None,
        officer_label(),
        &cclerk,
        &executor,
    )
    .expect("intermediate CI step 1 -> 2 commits");
    let cursor = executor.cell_state(cclerk.cell_id()).unwrap().fields[STEP_CURSOR_SLOT as usize];
    assert_eq!(
        cursor,
        field_from_u64(2),
        "one step from the charter terminal"
    );
    (cclerk, executor, app, intermediate)
}

#[test]
fn the_planned_hash_names_the_terminal_advance_turn_before_it_runs() {
    let (cclerk, executor, app, _intermediate) = charter_one_step_from_terminal(0x3b);

    // NAME the terminal turn (cursor 2 -> 3) before it runs.
    let planned = planned_advance_turn_hash(&app, &cclerk, &executor, officer_label())
        .expect("the mandate cell has live state");

    // Fire the terminal step through the SIGNING path.
    let terminal = fire_advance_step_signed(
        &app,
        &AuthRequired::None,
        officer_label(),
        &cclerk,
        &executor,
        HOST_SEED,
    )
    .expect("the terminal CI step commits (2 -> 3, at the charter terminal)");

    assert_eq!(
        terminal.turn_hash, planned,
        "the plan named EXACTLY the terminal turn that ran"
    );
    assert_eq!(
        terminal.finality,
        Finality::Final,
        "the terminal receipt is finalized"
    );
    assert!(
        terminal.executor_signature.is_some(),
        "the grain host signed the terminal receipt"
    );
    let cursor = executor.cell_state(cclerk.cell_id()).unwrap().fields[STEP_CURSOR_SLOT as usize];
    assert_eq!(
        cursor,
        field_from_u64(3),
        "the charter reached its terminal"
    );

    // GENUINELY executor-signed against the host pubkey (the exact check the forge runs).
    let host_pubkey = executor
        .executor_pubkey()
        .expect("the host key is installed");
    assert!(
        verify_receipt_signature_with_keys(&terminal, &[host_pubkey]).is_ok(),
        "the terminal receipt verifies against the host's executor key"
    );
    assert!(
        verify_receipt_signature_with_keys(&terminal, &[wrong_pubkey()]).is_err(),
        "a wrong host key is refused"
    );
}

#[test]
fn pole_i_non_terminal_charter_never_lands_the_pr() {
    let (cclerk, executor, app, intermediate) = charter_one_step_from_terminal(0x3b);

    // The forge binds the required check to the (yet-to-run) TERMINAL turn.
    let planned =
        planned_advance_turn_hash(&app, &cclerk, &executor, officer_label()).expect("live state");
    let host_pubkey = executor.executor_pubkey().unwrap();

    let mut pr = clean_pr().with_required_check(RequiredCheck::committed_receipt(
        "ci-complete",
        planned,
        vec![host_pubkey],
    ));
    let mut doc = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, true);
    let pre = doc.state_commitment();

    // POLE (i)a — NO witness: the charter has not produced the terminal receipt.
    match pr.land(&mut doc) {
        Err(PullRequestError::CheckNotSatisfied { check, reason }) => {
            assert_eq!(check.as_str(), "ci-complete");
            assert!(matches!(reason, CheckRefusal::NoWitness), "{reason:?}");
        }
        other => panic!("expected CheckNotSatisfied(NoWitness), got {other:?}"),
    }
    assert_eq!(doc.state_commitment(), pre, "no merge turn ran");
    assert_eq!(*doc.graph(), pr.base().replay(), "base fold byte-untouched");

    // POLE (i)b — a NON-TERMINAL step's receipt (genuine + signed, but the wrong
    // turn): the check names the terminal turn, so a mid-charter receipt is refused.
    assert!(
        intermediate.executor_signature.is_some(),
        "the intermediate step is signed"
    );
    assert_ne!(
        intermediate.turn_hash, planned,
        "it is NOT the terminal turn"
    );
    pr.present_witness("ci-complete", CheckWitness::Receipt(intermediate));
    match pr.land(&mut doc) {
        Err(PullRequestError::CheckNotSatisfied { reason, .. }) => {
            assert!(
                matches!(reason, CheckRefusal::WrongTurn { .. }),
                "a non-terminal receipt names the wrong turn, got {reason:?}"
            );
        }
        other => panic!("expected CheckNotSatisfied(WrongTurn), got {other:?}"),
    }
    assert_eq!(*doc.graph(), pr.base().replay(), "still nothing merged");
}

#[test]
fn pole_ii_terminal_charter_lands_the_pr_and_a_wrong_key_is_refused() {
    let (cclerk, executor, app, _intermediate) = charter_one_step_from_terminal(0x3b);

    // Bind the forge check to the terminal turn hash + the host's key.
    let planned =
        planned_advance_turn_hash(&app, &cclerk, &executor, officer_label()).expect("live state");
    let host_pubkey = executor.executor_pubkey().unwrap();

    // Drive the charter to TERMINAL through the signing path.
    let terminal = fire_advance_step_signed(
        &app,
        &AuthRequired::None,
        officer_label(),
        &cclerk,
        &executor,
        HOST_SEED,
    )
    .expect("the terminal CI step commits");
    assert_eq!(terminal.turn_hash, planned);

    // POLE (ii): the signed terminal receipt SATISFIES the check → the PR LANDS.
    let mut pr = clean_pr().with_required_check(RequiredCheck::committed_receipt(
        "ci-complete",
        planned,
        vec![host_pubkey],
    ));
    let mut doc = ExecutorDrivenDoc::new_at(&pr.base().replay(), 1, 2, true);
    pr.present_witness("ci-complete", CheckWitness::Receipt(terminal.clone()));
    pr.checks_satisfied()
        .expect("the signed terminal receipt satisfies the CI check");
    let receipts = pr.land(&mut doc).expect("a CI-green PR lands");
    assert!(!receipts.is_empty(), "the merge drove real turns");
    for r in &receipts {
        assert_eq!(r.finality, Finality::Final);
    }
    assert_eq!(
        *doc.graph(),
        pr.merge().unwrap().graph,
        "the landed document is the reviewed pushout (both sides' edits)"
    );
    assert!(doc.commitment_matches_projection());

    // WRONG-KEY REFUSAL: the SAME terminal receipt, but the check trusts a DIFFERENT
    // host key → the executor signature does not verify → refused, nothing merged.
    let mut pr_wrong = clean_pr().with_required_check(RequiredCheck::committed_receipt(
        "ci-complete",
        planned,
        vec![wrong_pubkey()],
    ));
    pr_wrong.present_witness("ci-complete", CheckWitness::Receipt(terminal));
    match pr_wrong.checks_satisfied() {
        Err(PullRequestError::CheckNotSatisfied { reason, .. }) => {
            assert!(
                matches!(reason, CheckRefusal::SignatureUnverified),
                "a wrong trusted-key set refuses the signed receipt, got {reason:?}"
            );
        }
        other => panic!("expected CheckNotSatisfied(SignatureUnverified), got {other:?}"),
    }
    let mut doc_wrong = ExecutorDrivenDoc::new_at(&pr_wrong.base().replay(), 3, 4, true);
    assert!(
        pr_wrong.land(&mut doc_wrong).is_err(),
        "a wrong-key check never lands the PR"
    );
    assert_eq!(
        *doc_wrong.graph(),
        pr_wrong.base().replay(),
        "nothing merged"
    );
}
