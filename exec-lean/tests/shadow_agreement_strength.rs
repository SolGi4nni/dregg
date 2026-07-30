//! shadow_agreement_strength.rs — **ASSERT THE STRENGTH, not just the bit.**
//!
//! # The standing hole this closes
//!
//! `ShadowAgreement` exists precisely to stop the harness calling a commit-bit coincidence "full
//! executor agreement": `FullState { agreed }` is a genuine CELL-BY-CELL denotational comparison of
//! the verified Lean executor's reconstituted post-state against the Rust one; `CommitBitOnly` is
//! the honestly-weaker check for turns off the root-agreeing set.
//!
//! ⚑ Until this file, **no test anywhere asserted which one a real turn produced** — the strength
//! was only ever `tracing`-logged, and `maybe_shadow_turn` threw it away (`let _ = …` at the single
//! call site). That is exactly how an always-red `FullState` detector survived NINE DAYS: it
//! compared a BLAKE3 sub-ledger root against an 8-felt whole-context anchor, so
//! `FullState { agreed: false }` fired on every honest turn and the warning meant nothing. A
//! detector no test can read is a detector no test can find broken.
//!
//! Both faces are pinned here against the LIVE FFI:
//!   * `FullState { agreed: true }` on a root-agreeing turn both executors commit — the strong
//!     claim, and the one that was stuck false;
//!   * `CommitBitOnly` on a turn OUTSIDE the root-agreeing set — the honestly-weaker claim, so a
//!     future change that quietly promoted everything to `FullState` fails here.
//!
//! No env var, no thread-local: the comparison is driven through `shadow_agreement_for` with
//! explicit pre/post ledgers, which is the same code path `maybe_shadow_turn` runs.
//!
//! Requires the linked Lean archive; self-skips when absent (PANICS under `DREGG_TEST_REQUIRE_LEAN=1`).

use std::collections::HashMap;

use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger, Permissions};
use dregg_exec_lean::{ShadowAgreement, shadow_agreement_for};
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

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn turn_with(agent: CellId, effects: Vec<Effect>) -> Turn {
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
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000),
        previous_receipt_hash: None,
        depends_on: vec![],
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

fn wide_field() -> FieldElement {
    [
        0x93, 0x4e, 0x47, 0xf2, 0x22, 0x21, 0x69, 0x76, 0xec, 0xab, 0xcd, 0x76, 0xf8, 0xbe, 0x42,
        0xed, 0x45, 0x9e, 0x23, 0xb1, 0x2e, 0x98, 0x8a, 0xb7, 0xad, 0x7a, 0x7d, 0xa3, 0x27, 0xd6,
        0x80, 0x64,
    ]
}

fn skip_no_lean() -> bool {
    !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (lean_available)",
    )
}

/// Run the Rust executor to get the honest post-state, then ask for the shadow agreement over
/// (pre, post) — the same shape `TurnExecutor::execute` hands the observer.
fn agreement_for(pre: &Ledger, turn: &Turn) -> (bool, ShadowAgreement) {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    // ⚠ The host ctx must be the EXECUTOR'S OWN — the same one `produce_via_lean` builds and the
    // same one the production observer is handed. It carries the block height the reconstitution
    // stamps into every forest-touched cell (`apply_committed_height`), so a host that disagrees
    // with the executor's clock makes the two post-states differ for a reason that has nothing to
    // do with the executors agreeing. (Measured: `diag()` at height 1 against a fresh executor at
    // height 0 diverges on exactly that stamp.)
    let host = executor.build_shadow_host_ctx(turn, pre);
    let mut post = pre.clone();
    let result = executor.execute(turn, &mut post);
    shadow_agreement_for(turn, pre, &host, result.is_committed(), &post)
        .expect("the turn must be comparable (marshallable + the FFI ran)")
}

/// ⚑ THE STRONG FACE. A root-agreeing turn both executors commit yields `FullState { agreed: true }`
/// — a genuine cell-by-cell denotational agreement, NOT a commit-bit coincidence.
///
/// This is the assertion that was missing while the detector was stuck at `agreed: false`.
#[test]
fn a_root_agreeing_committing_turn_yields_full_state_agreement() {
    if skip_no_lean() {
        return;
    }
    let agent = make_open_cell(1, 100);
    let agent_id = agent.id();
    let mut pre = Ledger::new();
    pre.insert_cell(agent).unwrap();

    // A full-width SetField — root-agreeing since the carrier widening, so it exercises the
    // denotational leg on exactly the shape that used to be fenced off it entirely.
    let turn = turn_with(
        agent_id,
        vec![Effect::SetField {
            cell: agent_id,
            index: 6,
            value: wide_field(),
        }],
    );

    let (lean_committed, agreement) = agreement_for(&pre, &turn);
    assert!(
        lean_committed,
        "the verified executor commits the self-write"
    );
    assert_eq!(
        agreement,
        ShadowAgreement::FullState { agreed: true },
        "a root-agreeing, both-committing turn must produce a GENUINE full-state agreement. \
         `FullState {{ agreed: false }}` means the two executors' post-states really differ (or the \
         comparison is comparing unlike things again); `CommitBitOnly` means the strong leg was \
         silently skipped"
    );
    assert!(
        agreement.is_full_state(),
        "and it must be reported at full strength, not laundered as a commit-bit check"
    );
}

/// ⚑ THE WEAK FACE, stated honestly. A turn OUTSIDE the root-agreeing set (here: a `NoteSpend`,
/// which grows an executor-owned accumulator the Lean post-image does not return) must report
/// `CommitBitOnly` — never `FullState`. A change that promoted everything to `FullState` to make
/// the strong assertion above pass would fail HERE.
#[test]
fn a_root_gap_turn_reports_only_commit_bit_strength() {
    if skip_no_lean() {
        return;
    }
    let agent = make_open_cell(2, 100);
    let agent_id = agent.id();
    let mut pre = Ledger::new();
    pre.insert_cell(agent).unwrap();

    let turn = turn_with(
        agent_id,
        vec![Effect::NoteSpend {
            nullifier: dregg_cell::Nullifier([0x11; 32]),
            note_tree_root: [0x12; 32],
            spending_proof: vec![1, 2, 3],
            value: 0,
            asset_type: 0,
            value_commitment: None,
        }],
    );

    let (_lean_committed, agreement) = agreement_for(&pre, &turn);
    assert!(
        !agreement.is_full_state(),
        "a characterized root-GAP effect (NoteSpend grows the nullifier accumulator the Lean \
         post-image does not carry) CANNOT support the denotational claim — reporting FullState \
         here would be the overclaim ShadowAgreement exists to prevent, got {agreement:?}"
    );
    assert!(
        matches!(agreement, ShadowAgreement::CommitBitOnly { .. }),
        "…so the honest strength is CommitBitOnly, got {agreement:?}"
    );
}
