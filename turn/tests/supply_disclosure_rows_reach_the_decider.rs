//! ANTI-VACUITY FOR THE DELETED `declared_supply` CHANNEL: the rows the verified per-asset
//! conservation decider is handed are NON-EMPTY and CONTAIN THE SUPPLY DISCLOSURE.
//!
//! ## Why this file exists
//!
//! `TurnExecutor::check_per_asset_conservation*` used to take a
//! `declared_supply: &[DeclaredSupplyChange]` slice so a turn could ASSERT "this credit is a
//! disclosed mint" and have the assertion enter the conserved sum. Measured on 2026-07-28: **every
//! invocation in the tree passed `&[]`** — the two atomic call sites, the cleartext site, the
//! light-client bundle site, and all five test sites — so nothing would have noticed the
//! reconciliation breaking. It was deleted, because under the ratified supply model
//! (`.docs-history-noclaude/SUPPLY-MODEL.md`) a supply change is disclosed by a PAIRED LEDGER
//! DELTA: `apply_mint` debits the asset's issuer WELL and credits the holder, `apply_burn` is the
//! dual, and `CreateCell` cannot open a balance at all.
//!
//! Deleting an always-empty parameter is easy to do and easy to LAUNDER — the gate would look the
//! same either way, and `check_per_asset_conservation_by_asset` short-circuits on an empty row set
//! (`if entries.is_empty() { return Ok(()) }`), so a pole that reached that line would prove
//! nothing at all. This file refuses to rest on that. It installs a RECORDING oracle at the exact
//! seam the verified Lean decider occupies and reads back the rows the decision was actually taken
//! over, for both poles:
//!
//! * **DISCLOSED** — a cap-gated `Effect::Mint` of 989. Two rows, SAME asset class, `+989` and
//!   `−989`. The `−989` is the issuer well's leg: the disclosure, as auditable ledger state rather
//!   than an unbacked claim, and gated by `holds_mint_authority` (the Rust image of Lean
//!   `mintAuthorizedB`) — which a `DeclaredSupplyChange` row was not.
//! * **MISDIRECTED** — the same mint with asset 7's issuer well registered to a cell of asset 9.
//!   Two rows, TWO DIFFERENT classes, so asset 7 gained 989 nothing paid for. REFUSED.
//!
//! The two poles are a CONTROLLED comparison: identical ledger shape, identical turn, identical
//! capabilities, and exactly ONE difference — the currency the registered issuer well lives in.
//! (`register_issuer_well` is an operator override and does not check that the registered well
//! shares the asset. The LAZILY-DERIVED well, which always shares it by construction, is exercised
//! by `executor::atomic::hardening_tests::disclosed_mint_reconciles_through_the_issuer_well_and_commits`.)
//!
//! ## What this file does NOT claim
//!
//! The `Σδ = 0` RULE is Lean-authored (`Dregg2.Circuit.CrossCellConserveDecision`, `@[export]
//! dregg_cross_cell_conserves`) and this file does not restate it — the recording oracle decides
//! honestly only so the run reaches a verdict; the assertions are about the ROW SET Rust gathers,
//! which is Rust's half of the job. `dregg-turn` cannot link `libdregg_lean.a` (that is
//! `dregg-exec-lean`, which depends on `dregg-turn`), so no test binary here can install the real
//! backend. Nothing here is evidence about the Lean decision procedure.

use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::{Cell, Ledger, Preconditions};
use dregg_turn::action::{Action, Authorization, DelegationMode, Effect};
use dregg_turn::executor::ConservationOracle;
use dregg_turn::{AtomicTurnError, ComputronCosts, MixedAtomicTurn, TurnExecutor};
use std::sync::Mutex;

/// The rows every `conserves` call was handed, in call order. Read back after each turn so the
/// assertions are about the ACTUAL decision input, not a reconstruction.
static SEEN: Mutex<Vec<Vec<(u32, i64)>>> = Mutex::new(Vec::new());

/// A per-asset `Σδ=0` decider that RECORDS its input and then decides honestly. Test-crate only:
/// never compiled into the library, let alone a node.
struct RecordingConservationOracle;

impl ConservationOracle for RecordingConservationOracle {
    fn conserves(&self, rows: &[(u32, i64)]) -> Result<(), (u32, i64)> {
        SEEN.lock().unwrap().push(rows.to_vec());
        let mut sums: std::collections::BTreeMap<u32, i64> = std::collections::BTreeMap::new();
        for (asset, delta) in rows {
            *sums.entry(*asset).or_insert(0) += *delta;
        }
        for (asset, sum) in sums {
            if sum != 0 {
                return Err((asset, sum));
            }
        }
        Ok(())
    }
}

fn take_rows() -> Vec<(u32, i64)> {
    let mut seen = SEEN.lock().unwrap();
    assert_eq!(
        seen.len(),
        1,
        "expected exactly ONE conservation decision for this turn, got {}",
        seen.len()
    );
    seen.pop().unwrap()
}

fn permissive() -> Permissions {
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

/// A permissive cell whose asset class is seeded by `asset` (byte 0 of the token id).
fn asset_cell(seed: u8, asset: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(31).wrapping_add(7);
    let mut token = [0u8; 32];
    token[0] = asset;
    let mut cell = Cell::with_balance(pk, token, balance);
    cell.permissions = permissive();
    cell
}

fn mint_turn(
    agent: dregg_cell::CellId,
    holder: dregg_cell::CellId,
    amount: u64,
) -> MixedAtomicTurn {
    MixedAtomicTurn {
        agent,
        nonce: 0,
        fee: 0,
        sovereign_entries: vec![],
        hosted_actions: vec![Action {
            target: holder,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Mint {
                target: holder,
                slot: 0,
                amount,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        }],
    }
}

/// One `#[test]` per binary: the conservation oracle is a process-wide `OnceLock`.
#[test]
fn the_conserved_row_set_carries_the_issuer_well_leg_and_the_gate_decides_on_it() {
    dregg_turn::executor::install_conservation_oracle(Box::new(RecordingConservationOracle))
        .expect("no oracle should be installed yet in this fresh test process");

    // ── POLE 1: THE DISCLOSED MINT. Two rows, one asset, they cancel. ───────────────────────────
    let mut ledger = Ledger::new();
    let holder = asset_cell(0xD9, 7, 0);
    let holder_id = holder.id();
    let asset7 = *holder.asset().as_bytes();
    ledger.insert_cell(holder).unwrap();

    // The issuer well of asset 7, in asset 7 — the CORRECT registration.
    let well = asset_cell(0xE9, 7, 0);
    let well_id = well.id();
    ledger.insert_cell(well).unwrap();

    let mut agent = asset_cell(0xA9, 0, 1_000);
    agent
        .capabilities
        .grant_faceted(well_id, AuthRequired::None, dregg_cell::EFFECT_MINT)
        .unwrap();
    agent
        .capabilities
        .grant(holder_id, AuthRequired::None)
        .unwrap();
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.register_issuer_well(asset7, well_id);
    executor
        .execute_mixed_atomic(&mint_turn(agent_id, holder_id, 989), &mut ledger)
        .expect("a mint whose issuer-well leg is present must COMMIT");

    let mut rows = take_rows();
    rows.sort_unstable();
    assert_eq!(
        rows.len(),
        2,
        "THE ANTI-VACUITY ASSERTION: the decision was taken over a NON-EMPTY row set — a mint \
         contributes BOTH legs, so the gate's `entries.is_empty()` short-circuit was not what \
         admitted this turn. Got {rows:?}"
    );
    let class7 = dregg_circuit::block_conservation::fold_token_id_to_asset(&asset7).as_u32();
    assert_eq!(
        rows,
        vec![(class7, -989), (class7, 989)],
        "the disclosed mint reaches the decider as +989 (holder) and −989 (ISSUER WELL) of the \
         SAME asset class — the well's leg IS the disclosure the deleted DeclaredSupplyChange row \
         was standing in for"
    );
    assert_eq!(
        ledger.get(&well_id).unwrap().state.balance(),
        -989,
        "and it is real ledger state, not a claim attached to the turn"
    );

    // ── POLE 2: THE MISDIRECTED DISCLOSURE. Two rows, TWO classes, REFUSED. ─────────────────────
    // `register_issuer_well` is an operator override and does not check that the registered well
    // shares the asset. Point asset 7's well at a cell of asset 9: the mint applies, but the
    // supply increase of asset 7 is funded by nothing in asset 7.
    let mut ledger = Ledger::new();
    let holder = asset_cell(0xDA, 7, 0);
    let holder_id = holder.id();
    ledger.insert_cell(holder).unwrap();

    let foreign_well = asset_cell(0xEA, 9, 0);
    let foreign_well_id = foreign_well.id();
    let asset9 = *foreign_well.asset().as_bytes();
    ledger.insert_cell(foreign_well).unwrap();

    let class9 = dregg_circuit::block_conservation::fold_token_id_to_asset(&asset9).as_u32();
    assert_ne!(
        class7, class9,
        "fixture assets must not share a fold class, or the refusal below would be the \
         collision guard rather than the conservation gate"
    );

    let mut agent = asset_cell(0xAB, 0, 1_000);
    agent
        .capabilities
        .grant_faceted(foreign_well_id, AuthRequired::None, dregg_cell::EFFECT_MINT)
        .unwrap();
    agent
        .capabilities
        .grant(holder_id, AuthRequired::None)
        .unwrap();
    let agent_id = agent.id();
    ledger.insert_cell(agent).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.register_issuer_well(asset7, foreign_well_id);

    match executor.execute_mixed_atomic(&mint_turn(agent_id, holder_id, 989), &mut ledger) {
        Err(AtomicTurnError::PerAssetConservationViolation { asset, imbalance }) => {
            assert!(
                (asset == class7 && imbalance == 989) || (asset == class9 && imbalance == -989),
                "the refusal names the un-funded class and its imbalance, got ({asset}, {imbalance})"
            );
        }
        other => panic!(
            "a mint whose disclosure leg lands in ANOTHER currency must be REFUSED as a per-asset \
             conservation violation, got {other:?}"
        ),
    }

    let mut rows = take_rows();
    rows.sort_unstable();
    assert_eq!(
        rows,
        {
            let mut expected = vec![(class7, 989_i64), (class9, -989_i64)];
            expected.sort_unstable();
            expected
        },
        "the SAME two-row shape as pole 1, differing only in which CLASS the disclosure landed \
         in — so the verdict flip is the arithmetic over the rows, not the presence or absence \
         of a disclosure row"
    );

    // Atomicity: nothing survived the refusal.
    assert_eq!(ledger.get(&holder_id).unwrap().state.balance(), 0);
    assert_eq!(ledger.get(&foreign_well_id).unwrap().state.balance(), 0);
}
