//! Property-test the RUNNING Rust `TurnExecutor` against the invariants the Lean
//! `Dregg2/` proves about the abstract model.
//!
//! The thesis (per the threat-model doc): "Lean proves X" is NOT "the running
//! Rust enforces X". Each test here builds an ADVERSARIAL turn that tries to
//! violate a proven invariant on the CONCRETE executor and asserts the running
//! system REJECTS it (or no-ops it, leaving state untouched). A divergence —
//! Lean proves it safe but the Rust executor ACCEPTS the attack — is a real bug.
//!
//! Invariants attacked:
//!   1. CONSERVATION    — no value minted or burned by a Transfer turn.
//!   2. AUTHORITY       — a turn with no/forged authorization cannot commit a
//!                        state change to a cell that requires a signature.
//!   3. NO-OVERFLOW-MINT— a Transfer that would overflow the destination is
//!                        rejected (no wrap-around credit).
//!   4. NO-DOUBLE-SPEND — a cell cannot send more than its balance, even across
//!                        a multi-effect turn (atomic rollback on failure).
//!   5. NO-REPLAY       — a committed turn replayed at the same nonce is rejected.
//!
//! Every adversarial turn here is built to PASS the shallow checks (agent
//! exists, nonce matches, fee covered) so the attack reaches the deep
//! enforcement — this is not security theater against the empty-forest guard.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use ed25519_dalek::{Signer, SigningKey, VerifyingKey};
use std::collections::HashMap;

use dregg_turn::action::{symbol, Action, Authorization, DelegationMode, Effect};
use dregg_turn::forest::CallForest;
use dregg_turn::turn::Turn;
use dregg_turn::{ComputronCosts, TurnExecutor};
use proptest::prelude::*;

// ============================================================================
// adversary toolkit
// ============================================================================

struct Kp {
    sk: SigningKey,
    pk: [u8; 32],
}
impl Kp {
    fn seed(b: u8) -> Self {
        let mut s = [0u8; 32];
        s[0] = b;
        let sk = SigningKey::from_bytes(&s);
        let pk: VerifyingKey = (&sk).into();
        Kp {
            sk,
            pk: pk.to_bytes(),
        }
    }
    /// A real signature over the action's canonical signing message.
    fn sign(&self, action: &Action) -> Authorization {
        let msg = TurnExecutor::compute_signing_message(action, &[0u8; 32]);
        Authorization::from_sig_bytes(self.sk.sign(&msg).to_bytes())
    }
}

fn open_cell(seed: u8, balance: i64) -> (Cell, Kp) {
    let kp = Kp::seed(seed);
    let mut cell = Cell::with_balance(kp.pk, [0u8; 32], balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    (cell, kp)
}

/// A cell whose `send` requires a real Signature — the authority test target.
fn sig_cell(seed: u8, balance: i64) -> (Cell, Kp) {
    let kp = Kp::seed(seed);
    // Default Cell permissions require Signature; keep them.
    (Cell::with_balance(kp.pk, [0u8; 32], balance), kp)
}

fn total_balance(ledger: &Ledger, ids: &[CellId]) -> u128 {
    ids.iter()
        .map(|id| {
            ledger
                .get(id)
                .map(|c| c.state.balance() as u128)
                .unwrap_or(0)
        })
        .sum()
}

fn transfer_turn(
    from: CellId,
    to: CellId,
    amount: u64,
    nonce: u64,
    auth: Authorization,
    prev: Option<[u8; 32]>,
) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: from,
        method: symbol("submit"),
        args: vec![],
        authorization: auth,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer { from, to, amount }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent: from,
        nonce,
        fee: 0,
        memo: None,
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: prev,
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

// ============================================================================
// 1. CONSERVATION — no value minted or burned (running executor)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]

    /// Adversary submits arbitrary (from,to,amount) transfers — some valid, many
    /// over-balance — and we assert total ledger value NEVER changes regardless
    /// of which commit / which reject. Mirrors Lean conservation on the running
    /// Rust executor.
    #[test]
    fn conservation_holds_under_adversarial_transfers(
        ops in proptest::collection::vec((0usize..3, 0usize..3, any::<u64>()), 1..40)
    ) {
        let mut ledger = Ledger::new();
        let mut ids = vec![];
        for s in 0..3u8 {
            let (mut c, _) = open_cell(s + 1, 10_000);
            // grant each cell a cap to every other (open ledger).
            for t in 0..3u8 {
                if t != s {
                    let (other, _) = open_cell(t + 1, 0);
                    c.capabilities.grant(other.id(), AuthRequired::None);
                }
            }
            let id = c.id();
            ledger.insert_cell(c).unwrap();
            ids.push(id);
        }
        let initial = total_balance(&ledger, &ids);
        let exec = TurnExecutor::new(ComputronCosts::zero());

        for (fi, ti, amt) in ops {
            if fi == ti { continue; }
            let (from, to) = (ids[fi], ids[ti]);
            let nonce = ledger.get(&from).unwrap().state.nonce();
            let prev = exec.get_last_receipt_hash(&from);
            let turn = transfer_turn(from, to, amt, nonce, Authorization::Unchecked, prev);
            let _ = exec.execute(&turn, &mut ledger);
            // The invariant must hold after EVERY step, not just at the end.
            prop_assert_eq!(
                total_balance(&ledger, &ids),
                initial,
                "CONSERVATION VIOLATED (running Rust): value minted or burned by a transfer"
            );
        }
    }
}

// ============================================================================
// 2. AUTHORITY — no unauthorized commit
// ============================================================================

/// A cell that requires a Signature to send must REJECT a turn that carries no
/// valid authorization. The attacker tries `Unchecked` (the historical bypass)
/// and a signature from the WRONG key. Both must fail-closed, leaving balances
/// untouched. This is the "no unauthorized commit" invariant on the running Rust.
#[test]
fn unauthorized_transfer_is_rejected_and_state_unchanged() {
    // Victim cell requires a signature to send; attacker does NOT hold its key.
    let (victim, _victim_kp) = sig_cell(7, 5_000);
    let (recipient, _) = open_cell(8, 0);
    let victim_id = victim.id();
    let recipient_id = recipient.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(victim).unwrap();
    ledger.insert_cell(recipient).unwrap();

    let exec = TurnExecutor::new(ComputronCosts::zero());
    let initial = total_balance(&ledger, &[victim_id, recipient_id]);
    let victim_bal = ledger.get(&victim_id).unwrap().state.balance();

    // Attack A: Authorization::Unchecked against a signature-required cell.
    let nonce = ledger.get(&victim_id).unwrap().state.nonce();
    let t_unchecked = transfer_turn(
        victim_id,
        recipient_id,
        5_000,
        nonce,
        Authorization::Unchecked,
        None,
    );
    let r1 = exec.execute(&t_unchecked, &mut ledger);
    assert!(
        !r1.is_committed(),
        "FINDING: Authorization::Unchecked committed a transfer from a signature-required cell"
    );

    // Attack B: a real signature, but from the WRONG key (the attacker's), over
    // the right action.
    let wrong = Kp::seed(99);
    let action = Action {
        target: victim_id,
        method: symbol("submit"),
        args: vec![],
        authorization: Authorization::Unchecked, // placeholder; replaced below
        preconditions: Default::default(),
        effects: vec![Effect::Transfer {
            from: victim_id,
            to: recipient_id,
            amount: 5_000,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    let forged_auth = wrong.sign(&action);
    let nonce = ledger.get(&victim_id).unwrap().state.nonce();
    let t_forged = transfer_turn(victim_id, recipient_id, 5_000, nonce, forged_auth, None);
    let r2 = exec.execute(&t_forged, &mut ledger);
    assert!(
        !r2.is_committed(),
        "FINDING: a signature from the WRONG key committed a transfer (forgery accepted)"
    );

    // Authority invariant: balances unchanged, no value moved.
    assert_eq!(
        total_balance(&ledger, &[victim_id, recipient_id]),
        initial,
        "FINDING: total value changed despite both unauthorized attempts being rejected"
    );
    assert_eq!(
        ledger.get(&victim_id).unwrap().state.balance(),
        victim_bal,
        "FINDING: victim balance changed under an unauthorized transfer"
    );
}

// ============================================================================
// 3. NO-OVERFLOW-MINT — overflow at the destination is rejected
// ============================================================================

/// A transfer that would overflow u64 at the destination must be rejected, NOT
/// wrap around to a small credit (which would mint value out of thin air).
#[test]
fn destination_overflow_does_not_mint() {
    // signed-wells (ac01f9b7b): balances are i64; the overflow boundary is now
    // i64::MAX. Intent preserved: a transfer that would overflow the balance
    // type must be rejected (no wrap-around mint).
    let (mut sender, _) = open_cell(11, i64::MAX);
    let (recipient, _) = open_cell(12, i64::MAX);
    sender
        .capabilities
        .grant(recipient.id(), AuthRequired::None);
    let sid = sender.id();
    let rid = recipient.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(sender).unwrap();
    ledger.insert_cell(recipient).unwrap();

    let exec = TurnExecutor::new(ComputronCosts::zero());
    let before = total_balance(&ledger, &[sid, rid]);

    // recipient already at i64::MAX; any positive transfer overflows.
    let nonce = ledger.get(&sid).unwrap().state.nonce();
    let turn = transfer_turn(sid, rid, 1, nonce, Authorization::Unchecked, None);
    let r = exec.execute(&turn, &mut ledger);
    assert!(
        !r.is_committed(),
        "FINDING: overflowing transfer committed (wrap-around mint)"
    );
    assert_eq!(
        total_balance(&ledger, &[sid, rid]),
        before,
        "FINDING: total value changed on a rejected overflow transfer"
    );
    assert_eq!(ledger.get(&rid).unwrap().state.balance(), i64::MAX);
}

// ============================================================================
// 4. NO-DOUBLE-SPEND — multi-effect turn cannot overspend; atomic rollback
// ============================================================================

/// A single turn with TWO transfers that together exceed the sender's balance
/// must NOT partially apply: the second (over-balance) transfer fails and the
/// whole turn rolls back. Net: the sender cannot spend the same coins twice.
#[test]
fn multi_effect_overspend_rolls_back_atomically() {
    let (mut sender, _) = open_cell(21, 100);
    let (a, _) = open_cell(22, 0);
    let (b, _) = open_cell(23, 0);
    sender.capabilities.grant(a.id(), AuthRequired::None);
    sender.capabilities.grant(b.id(), AuthRequired::None);
    let (sid, aid, bid) = (sender.id(), a.id(), b.id());

    let mut ledger = Ledger::new();
    ledger.insert_cell(sender).unwrap();
    ledger.insert_cell(a).unwrap();
    ledger.insert_cell(b).unwrap();

    let exec = TurnExecutor::new(ComputronCosts::zero());
    let before = total_balance(&ledger, &[sid, aid, bid]);

    // Effect 1: send 80 (ok). Effect 2: send 80 again (only 20 left → fail).
    let mut forest = CallForest::new();
    let action = Action {
        target: sid,
        method: symbol("submit"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![
            Effect::Transfer {
                from: sid,
                to: aid,
                amount: 80,
            },
            Effect::Transfer {
                from: sid,
                to: bid,
                amount: 80,
            },
        ],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    let nonce = ledger.get(&sid).unwrap().state.nonce();
    let turn = Turn {
        agent: sid,
        nonce,
        fee: 0,
        memo: None,
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };
    let r = exec.execute(&turn, &mut ledger);
    assert!(
        !r.is_committed(),
        "FINDING: an over-balance multi-transfer turn committed (double-spend)"
    );

    // ATOMICITY: neither transfer applied — sender keeps all 100, a/b stay 0.
    assert_eq!(
        ledger.get(&sid).unwrap().state.balance(),
        100,
        "FINDING: partial debit — first transfer was NOT rolled back"
    );
    assert_eq!(
        ledger.get(&aid).unwrap().state.balance(),
        0,
        "FINDING: partial credit leaked through rollback"
    );
    assert_eq!(ledger.get(&bid).unwrap().state.balance(), 0);
    assert_eq!(total_balance(&ledger, &[sid, aid, bid]), before);
}

// ============================================================================
// 5. NO-REPLAY — a committed turn cannot be re-applied at the same nonce
// ============================================================================

/// Commit a transfer, then REPLAY the identical turn (same nonce). The replay
/// must be rejected (NonceReplay) so the transfer cannot execute twice.
#[test]
fn replay_at_same_nonce_is_rejected() {
    let (mut sender, _) = open_cell(31, 1_000);
    let (recipient, _) = open_cell(32, 0);
    sender
        .capabilities
        .grant(recipient.id(), AuthRequired::None);
    let (sid, rid) = (sender.id(), recipient.id());

    let mut ledger = Ledger::new();
    ledger.insert_cell(sender).unwrap();
    ledger.insert_cell(recipient).unwrap();

    let exec = TurnExecutor::new(ComputronCosts::zero());

    let nonce0 = ledger.get(&sid).unwrap().state.nonce();
    let turn = transfer_turn(sid, rid, 100, nonce0, Authorization::Unchecked, None);

    // First application commits.
    let r1 = exec.execute(&turn, &mut ledger);
    assert!(r1.is_committed(), "setup: the first transfer should commit");
    assert_eq!(ledger.get(&rid).unwrap().state.balance(), 100);

    // Replay the SAME turn (still nonce0) — must be rejected.
    let r2 = exec.execute(&turn, &mut ledger);
    assert!(
        !r2.is_committed(),
        "FINDING: replayed turn at the same nonce committed AGAIN (replay attack succeeded)"
    );
    // Recipient still has exactly 100 — the transfer did not double-apply.
    assert_eq!(
        ledger.get(&rid).unwrap().state.balance(),
        100,
        "FINDING: replay double-applied the transfer (recipient credited twice)"
    );
    // Sender debited exactly once.
    assert_eq!(ledger.get(&sid).unwrap().state.balance(), 900);
}
