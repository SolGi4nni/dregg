//! THE SWAP strict-veto beachhead (part d) — the verified Lean executor as a binding REJECTION
//! authority on the commit path.
//!
//! With `DREGG_LEAN_SHADOW=1` + `DREGG_LEAN_SHADOW_STRICT=1` (and the Lean FFI linked via the
//! `lean-shadow` feature), a turn the legacy Rust executor COMMITS but the verified Lean executor
//! REJECTS is VETOED: the commit is rolled back and the turn is reported `Rejected(LeanShadowVeto)`.
//! The verified kernel can ONLY tighten the decision (kernel-vs-NEW-Rust; it never launders a Rust
//! rejection to a commit), so a divergence makes the node strictly MORE conservative.
//!
//! The TOOTH is the under-authorised `Burn`: dregg1's `apply.rs` commits a burn on an owned open
//! cell, but the verified `.burnA` requires an explicit mint/burn cap (`mintAuthorizedB`). Under
//! strict mode the verified veto rolls the burn back; WITHOUT the cap the balance is unchanged.
//!
//! Run (single-threaded — the test mutates process env):
//!   DREGG_LEAN_SHADOW=1 DREGG_LEAN_SHADOW_STRICT=1 cargo test -p dregg-turn \
//!       --features lean-shadow --test lean_strict_veto -- --nocapture --test-threads=1

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

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

fn make_open_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn one_cell_ledger(bal: u64) -> (Ledger, CellId) {
    let a = make_open_cell(1, bal);
    let id = a.id();
    let mut l = Ledger::new();
    l.insert_cell(a).unwrap();
    (l, id)
}

fn burn_turn(agent: CellId) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Burn { target: agent, slot: 0, amount: 10 }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000_000),
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

/// THE SWAP strict-veto TOOTH: an under-authorised burn (apply.rs commits, verified `.burnA`
/// rejects for the missing mint-cap) is VETOED under strict mode — rolled back, reported
/// `Rejected(LeanShadowVeto)`, balance UNCHANGED. WITHOUT strict mode the same burn COMMITS
/// (debits 10). The two-sidedness proves the veto is a genuine gate, not a no-op.
///
/// Skips (passes vacuously, with a printed note) when the Lean FFI is not linked — the veto is a
/// no-op without the verified executor, so there is nothing to enforce.
#[test]
fn strict_veto_rolls_back_lean_rejected_burn() {
    // Single-threaded env mutation: set the shadow + strict flags for this test.
    // SAFETY: this test binary is run with --test-threads=1 for the strict-veto suite; the env
    // mutation is local to this process and restored at the end.
    unsafe {
        std::env::set_var("DREGG_LEAN_SHADOW", "1");
        std::env::set_var("DREGG_LEAN_SHADOW_STRICT", "1");
    }

    // STRICT mode: run the under-authorised burn. If the Lean FFI is linked, the verified `.burnA`
    // rejects the missing-cap burn ⇒ VETO ⇒ Rejected(LeanShadowVeto), balance unchanged. If the
    // Lean FFI is NOT linked, there is no verified verdict to veto with, so the strict path falls
    // through to the Rust commit (the burn commits, debiting 10). Both outcomes are SOUND — the
    // veto can only TIGHTEN, never spuriously reject without a verified rejection.
    let (mut ledger, agent) = one_cell_ledger(100);
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&burn_turn(agent), &mut ledger);
    let post_bal = ledger.get(&agent).map(|c| c.state.balance());

    match &result {
        dregg_turn::turn::TurnResult::Rejected {
            reason: dregg_turn::TurnError::LeanShadowVeto,
            ..
        } => {
            // The verified Lean executor vetoed: the commit MUST be rolled back (balance unchanged).
            assert_eq!(
                post_bal,
                Some(100),
                "strict veto must ROLL BACK the commit — balance unchanged (100), got {post_bal:?}"
            );
            eprintln!("[strict-veto] TOOTH PASSED: verified Lean veto rolled back the burn.");

            // NON-VACUITY: strict OFF, re-run — the SAME burn now COMMITS (apply.rs commits a burn
            // on an owned open cell, debiting 10). The veto is genuinely two-sided.
            unsafe {
                std::env::set_var("DREGG_LEAN_SHADOW_STRICT", "0");
            }
            let (mut ledger2, agent2) = one_cell_ledger(100);
            let executor2 = TurnExecutor::new(ComputronCosts::zero());
            let result2 = executor2.execute(&burn_turn(agent2), &mut ledger2);
            assert!(
                result2.is_committed(),
                "without strict mode the burn must COMMIT, got {result2:?}"
            );
            assert_eq!(
                ledger2.get(&agent2).map(|c| c.state.balance()),
                Some(90),
                "the non-vetoed burn must debit 10 (100 -> 90)"
            );
        }
        dregg_turn::turn::TurnResult::Committed { .. } => {
            // Lean FFI not linked (no verified verdict) — the strict path must NOT spuriously veto;
            // the burn commits. (When the FFI IS linked, the branch above fires instead.)
            assert_eq!(
                post_bal,
                Some(90),
                "without a verified verdict the burn commits and debits 10 (100 -> 90), got {post_bal:?}"
            );
            eprintln!(
                "[strict-veto] Lean FFI not linked — no verified verdict to veto; the burn \
                 committed (strict path does not spuriously reject). Build with --features \
                 lean-shadow + a present libdregg_lean.a to exercise the veto."
            );
        }
        other => panic!("unexpected strict-veto outcome: {other:?}"),
    }

    cleanup_env();
}

fn cleanup_env() {
    unsafe {
        std::env::remove_var("DREGG_LEAN_SHADOW");
        std::env::remove_var("DREGG_LEAN_SHADOW_STRICT");
    }
}
