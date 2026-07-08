//! committed_height_effect_families.rs — GAP-1 RESIDUAL: is the PI-v3 committed-height fix complete
//! across EVERY cell-touching effect family, or did it close only the Transfer instance?
//!
//! # What this pins
//!
//! The SWAP fix (`lean_apply::apply_committed_height`, commit `7708ed4a3`) closed the Rust↔Lean
//! `.root()` divergence at `block_height > 0` — but its golden (`faucet_fee_well_divergence.rs`)
//! only exercised **Transfer**. `committed_height` folds into `compute_canonical_state_commitment`
//! (the last commitment limb) for EVERY forest-touched cell, regardless of effect family. So the
//! open question GAP-1 flagged: do `SetField` / `Seal` / `Destroy` / `SetPermissions` /
//! `SetVerificationKey` / `MakeSovereign` / cap-introduction / … ALSO agree at height > 0, or does
//! `committed_height_touched_cells` capture only Transfer's `{from, to}` write-set and drop the
//! cells the OTHER families journal?
//!
//! This is a height × effect-family matrix: for each committing, marshallable, cell-touching family
//! we run BOTH producers (Rust reference `TurnExecutor` == verified-Lean `execute_via_lean`) at
//! `block_height ∈ {0, 1, 7, 1_048_576}` and assert the post-state `.root()` AGREES (plus per-cell
//! balance / nonce / fields / cap_root / committed_height). A family that agrees at height 0 but
//! DIVERGES at height > 0 is a real lurking committed-height-class bug (the stamp replayed for
//! Transfer's touched cells but not for that family's). The height-0 column is the non-vacuous
//! control: it proves the family round-trips at all, so a height > 0 failure isolates the stamp.
//!
//! Requires the linked Lean archive (`lean-shadow` + `lean_available()`); self-skips when absent.

use std::collections::HashMap;

use dregg_cell::capability::CapabilityRef;
use dregg_cell::lifecycle::{DeathCertificate, DeathReason};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger, Permissions, VerificationKey};
use dregg_exec_lean::lean_apply::{self, execute_via_lean};
use dregg_exec_lean::lean_shadow::ShadowHostCtx;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

const HEIGHTS: &[u64] = &[0, 1, 7, 1_048_576];

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

/// A self-`node` capability — mint/burn authority over the cell itself (the delegator edge the
/// verified `recCDelegate`/`mintAuthorizedB` gates read).
fn grant_self_cap(cell: &mut Cell) {
    let id = cell.id();
    cell.capabilities.grant(id, AuthRequired::None);
}

fn field_from_u64(v: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
}

fn single_effect_turn(agent: CellId, target: CellId, effect: Effect) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
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

/// One effect-family fixture: a pre-state, the turn, and the cell ids whose per-cell state to check
/// (the full-ledger `.root()` is always compared regardless of this list).
struct Fixture {
    pre: Ledger,
    turn: Turn,
    ids: Vec<CellId>,
}

/// Compare two ledgers cell-by-cell (balance + nonce + state fields + cap_root + committed_height)
/// AND on the full-ledger `.root()`. `committed_height` is the limb under test — it is compared
/// EXPLICITLY (not just implicitly via the root) so a divergence names the family + height precisely.
fn ledgers_agree(rust: &mut Ledger, lean: &mut Ledger, ids: &[CellId]) -> Result<(), String> {
    for id in ids {
        let r = rust
            .get(id)
            .ok_or_else(|| format!("cell {id:?} missing from RUST ledger"))?;
        let l = lean
            .get(id)
            .ok_or_else(|| format!("cell {id:?} missing from LEAN ledger"))?;
        if r.state.balance() != l.state.balance() {
            return Err(format!(
                "balance divergence on {id:?}: rust={} lean={}",
                r.state.balance(),
                l.state.balance()
            ));
        }
        if r.state.nonce() != l.state.nonce() {
            return Err(format!(
                "nonce divergence on {id:?}: rust={} lean={}",
                r.state.nonce(),
                l.state.nonce()
            ));
        }
        for slot in 0..dregg_cell::state::STATE_SLOTS {
            if r.state.fields[slot] != l.state.fields[slot] {
                return Err(format!(
                    "field[{slot}] divergence on {id:?}: rust={:?} lean={:?}",
                    r.state.fields[slot], l.state.fields[slot]
                ));
            }
        }
        if r.state.committed_height() != l.state.committed_height() {
            return Err(format!(
                "COMMITTED_HEIGHT divergence on {id:?}: rust={} lean={} (the PI-v3 stamp was \
                 replayed for one family's touched-set but not this one)",
                r.state.committed_height(),
                l.state.committed_height()
            ));
        }
        let rc = dregg_cell::compute_canonical_capability_root(&r.capabilities);
        let lc = dregg_cell::compute_canonical_capability_root(&l.capabilities);
        if rc != lc {
            return Err(format!(
                "cap_root divergence on {id:?}: rust={rc:?} lean={lc:?}"
            ));
        }
    }
    let rr = rust.root();
    let lr = lean.root();
    if rr != lr {
        return Err(format!("ROOT divergence: rust={rr:?} lean={lr:?}"));
    }
    Ok(())
}

/// Run one family fixture through BOTH producers at `block_height` and return Ok(()) on full
/// agreement (per-cell + committed_height + `.root()`), else the first divergence. Both must commit.
fn run_family_at(fx: &Fixture, block_height: u64) -> Result<(), String> {
    // RUST reference: the chain height set to `block_height`; the executor stamps
    // `committed_height = self.block_height` onto every forest-touched (journaled) cell.
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_block_height(block_height);
    let mut rust_ledger = fx.pre.clone();
    let rust_result = executor.execute(&fx.turn, &mut rust_ledger);
    if !rust_result.is_committed() {
        return Err(format!(
            "Rust reference did not commit at height {block_height}: {rust_result:?}"
        ));
    }

    // LEAN producer: the host ctx carries the SAME block height, so the reconstitution replays the
    // identical committed-height stamp on the identical forest-touched cells.
    let host = ShadowHostCtx {
        block_height,
        ..ShadowHostCtx::diag()
    };
    let (mut lean_ledger, lean_committed) = match execute_via_lean(&fx.turn, &fx.pre, &host) {
        Ok(x) => x,
        Err(lean_apply::ExtractError::Ineligible) => {
            return Err("turn was Lean-ineligible (a marshaller GAP — no wire arm)".to_string());
        }
        Err(e) => return Err(format!("Lean state-producer path errored: {e}")),
    };
    if !lean_committed {
        return Err(format!(
            "commit-bit divergence at height {block_height}: Rust committed, Lean did not"
        ));
    }

    ledgers_agree(&mut rust_ledger, &mut lean_ledger, &fx.ids)
}

// =====================================================================================
// FIXTURE BUILDERS — one committing, marshallable, cell-touching turn per effect family.
// Each is height-agnostic: the height is threaded by `run_family_at`.
// =====================================================================================

fn fx_transfer() -> Fixture {
    let a = make_open_cell(1, 1_000);
    let b = make_open_cell(2, 0);
    let (a_id, b_id) = (a.id(), b.id());
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();
    let turn = single_effect_turn(
        a_id,
        a_id,
        Effect::Transfer {
            from: a_id,
            to: b_id,
            amount: 250,
        },
    );
    Fixture {
        pre,
        turn,
        ids: vec![a_id, b_id],
    }
}

fn fx_set_field() -> Fixture {
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    let turn = single_effect_turn(
        a_id,
        a_id,
        Effect::SetField {
            cell: a_id,
            index: 6,
            value: field_from_u64(42),
        },
    );
    Fixture {
        pre,
        turn,
        ids: vec![a_id],
    }
}

fn fx_increment_nonce() -> Fixture {
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    let turn = single_effect_turn(a_id, a_id, Effect::IncrementNonce { cell: a_id });
    Fixture {
        pre,
        turn,
        ids: vec![a_id],
    }
}

fn fx_revoke_capability() -> Fixture {
    // Revoke on an empty c-list: a no-op in Rust (cap_root stays the empty root) that STILL journals
    // the cell (`record_revoke_capability`) — so the committed-height stamp fires on it.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    let turn = single_effect_turn(
        a_id,
        a_id,
        Effect::RevokeCapability {
            cell: a_id,
            slot: 0,
        },
    );
    Fixture {
        pre,
        turn,
        ids: vec![a_id],
    }
}

fn fx_cell_seal() -> Fixture {
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    let turn = single_effect_turn(
        a_id,
        a_id,
        Effect::CellSeal {
            target: a_id,
            reason: [9u8; 32],
        },
    );
    Fixture {
        pre,
        turn,
        ids: vec![a_id],
    }
}

fn fx_cell_destroy() -> Fixture {
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    let certificate = DeathCertificate {
        cell_id: a_id,
        last_receipt_hash: [3u8; 32],
        final_state_commitment: [4u8; 32],
        destroyed_at_height: 12,
        reason: DeathReason::Voluntary,
    };
    let turn = single_effect_turn(
        a_id,
        a_id,
        Effect::CellDestroy {
            target: a_id,
            certificate,
        },
    );
    Fixture {
        pre,
        turn,
        ids: vec![a_id],
    }
}

fn fx_grant_capability_cross() -> Fixture {
    // A holds a self-edge (the delegator authority) and grants a full 7-field cap over A into B's
    // c-list. Rust journals ONLY the recipient B (`record_grant_capability(*to)`); the committed-
    // height stamp must land on B (not A, whose nonce bump is the unjournaled prologue).
    let mut a = make_open_cell(1, 100);
    grant_self_cap(&mut a);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();
    let cap = CapabilityRef {
        target: a_id,
        slot: 0,
        permissions: AuthRequired::Signature,
        breadstuff: Some([7u8; 32]),
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
    };
    let turn = single_effect_turn(
        a_id,
        a_id,
        Effect::GrantCapability {
            from: a_id,
            to: b_id,
            cap,
        },
    );
    Fixture {
        pre,
        turn,
        ids: vec![a_id, b_id],
    }
}

fn fx_attenuate_capability() -> Fixture {
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    a.capabilities.grant(b_id, AuthRequired::None);
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();
    let turn = single_effect_turn(
        a_id,
        a_id,
        Effect::AttenuateCapability {
            cell: a_id,
            slot: 0,
            narrower_permissions: AuthRequired::Signature,
            narrower_effects: None,
            narrower_expiry: Some(500),
        },
    );
    Fixture {
        pre,
        turn,
        ids: vec![a_id, b_id],
    }
}

fn fx_set_permissions() -> Fixture {
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    // Install a DIFFERENT (non-open) permission struct so the leaf genuinely moves.
    let mut new_perms = open_permissions();
    new_perms.send = AuthRequired::Signature;
    let turn = single_effect_turn(
        a_id,
        a_id,
        Effect::SetPermissions {
            cell: a_id,
            new_permissions: new_perms,
        },
    );
    Fixture {
        pre,
        turn,
        ids: vec![a_id],
    }
}

fn fx_set_verification_key() -> Fixture {
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    // `VerificationKey::new` computes `blake3(data)` as the hash — internally consistent, so
    // `apply_set_verification_key`'s integrity refusal (hash == blake3(data)) passes.
    let vk = VerificationKey::new(vec![1, 2, 3, 4, 5]);
    let turn = single_effect_turn(
        a_id,
        a_id,
        Effect::SetVerificationKey {
            cell: a_id,
            new_vk: Some(vk),
        },
    );
    Fixture {
        pre,
        turn,
        ids: vec![a_id],
    }
}

fn fx_make_sovereign() -> Fixture {
    // MakeSovereign REMOVES A from the ledger (no surviving leaf → not committed-height stamped); B
    // is an untouched bystander that must NOT be stamped on either side. The full-ledger `.root()`
    // (over B alone) is the comparison; A is excluded from `ids` since it is gone from both.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();
    let turn = single_effect_turn(a_id, a_id, Effect::MakeSovereign { cell: a_id });
    Fixture {
        pre,
        turn,
        ids: vec![b_id],
    }
}

fn families() -> Vec<(&'static str, Fixture)> {
    vec![
        ("Transfer", fx_transfer()),
        ("SetField", fx_set_field()),
        ("IncrementNonce", fx_increment_nonce()),
        ("RevokeCapability", fx_revoke_capability()),
        ("CellSeal", fx_cell_seal()),
        ("CellDestroy", fx_cell_destroy()),
        ("GrantCapability(cross)", fx_grant_capability_cross()),
        ("AttenuateCapability", fx_attenuate_capability()),
        ("SetPermissions", fx_set_permissions()),
        ("SetVerificationKey", fx_set_verification_key()),
        ("MakeSovereign", fx_make_sovereign()),
    ]
}

fn skip_no_lean() -> bool {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        true
    } else {
        false
    }
}

/// THE GAP-1 RESIDUAL MATRIX. Every cell-touching effect family × {0, 1, 7, 1_048_576}. A family
/// that agrees at height 0 but diverges at height > 0 is a residual committed-height-class bug.
#[test]
fn committed_height_agrees_across_effect_families_and_heights() {
    if skip_no_lean() {
        return;
    }
    let mut failures: Vec<String> = Vec::new();
    let mut ran = 0usize;
    for (name, fx) in families() {
        for &height in HEIGHTS {
            ran += 1;
            match run_family_at(&fx, height) {
                Ok(()) => {
                    eprintln!("OK    {name:<24} height={height}");
                }
                Err(why) => {
                    eprintln!("FAIL  {name:<24} height={height}: {why}");
                    failures.push(format!("{name} @ height {height}: {why}"));
                }
            }
        }
    }
    eprintln!(
        "committed-height matrix: {} cases ({} families × {} heights), {} failures",
        ran,
        families().len(),
        HEIGHTS.len(),
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "committed-height-class divergences (the fix is NOT uniform across families):\n  {}",
        failures.join("\n  ")
    );
}
