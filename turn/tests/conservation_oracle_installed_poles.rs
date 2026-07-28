//! THE OTHER POLE of `conservation_fails_closed_without_gate.rs`: with a conservation gate INSTALLED,
//! an HONEST turn still passes and a VIOLATING one is still refused.
//!
//! A fail-closed path that also breaks honest turns is not a fix, and "everything is refused" is not
//! a conservation gate. This file holds the environment fixed — same `DREGG_REQUIRE_LEAN=1`, same
//! turns, same ledger shape — and changes exactly ONE thing: a `ConservationOracle` is installed.
//! Both verdicts come back, and they come back as CONSERVATION verdicts
//! (`PerAssetConservationViolation` carrying the imbalance), not as the missing-gate refusal.
//!
//! ## What the oracle here is, stated plainly
//!
//! It is a **test-crate** oracle, not the verified one. `dregg-turn` cannot link `libdregg_lean.a`
//! (that is `dregg-exec-lean`, which depends on `dregg-turn`), so no test binary in this crate can
//! install the real `dregg_cross_cell_conserves` backend. This oracle lives in this test file only —
//! it is never compiled into the library, let alone a deployed node — and it exists to pin the SEAM:
//! that an installed oracle's verdict is the one the executor returns, and that installing one
//! restores honest turns. It is NOT evidence about the Lean decision procedure.
//!
//! The verified backend's own accept/refuse behaviour is exercised where the archive is actually
//! linked (`dregg-exec-lean`), and the Lean side carries
//! `CrossCellConserveRefine.decision_conserves_iff_air_boundary` — the theorem that the decision
//! equals the committed `CrossCellConservation` AIR boundary. Neither claim is made here.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::executor::ConservationOracle;
use dregg_turn::{ActionBuilder, ComputronCosts, TurnBuilder, TurnError, TurnExecutor};
use std::collections::BTreeMap;

/// A per-asset `Σδ=0` decider living in this TEST CRATE ONLY. Same shape as the seam's contract:
/// `Ok(())` admits, `Err((asset, imbalance))` names the first imbalanced asset in ascending key
/// order. Not verified, not shipped, and not a claim about the Lean decision.
struct TestConservationOracle;

impl ConservationOracle for TestConservationOracle {
    fn conserves(&self, rows: &[(u32, i64)]) -> Result<(), (u32, i64)> {
        let mut sums: BTreeMap<u32, i64> = BTreeMap::new();
        for (asset, delta) in rows.iter() {
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

fn open_cell(seed: u8, token_id: [u8; 32], balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let mut cell = Cell::with_balance(pk, token_id, balance);
    cell.permissions = open_permissions();
    cell
}

fn two_asset_ledger() -> (Ledger, CellId, CellId, CellId) {
    let token_x = [0x11u8; 32];
    let token_y = [0x22u8; 32];
    let cell_x = open_cell(2, token_x, 0);
    let cell_y = open_cell(3, token_y, 1_000_000);
    let (x_id, y_id) = (cell_x.id(), cell_y.id());

    let mut agent = open_cell(1, [0u8; 32], 5_000);
    agent.capabilities.grant(x_id, AuthRequired::None);
    agent.capabilities.grant(y_id, AuthRequired::None);
    let agent_id = agent.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(cell_x).unwrap();
    ledger.insert_cell(cell_y).unwrap();
    (ledger, agent_id, x_id, y_id)
}

/// One `#[test]` per binary: the oracle is a process-wide `OnceLock`, and this test mutates the
/// process environment.
#[test]
fn conservation_gate_installed_admits_honest_and_refuses_violating() {
    // SAFETY: this test binary contains exactly one `#[test]`, so no other thread is reading or
    // writing the environment while this runs. Set to the SAME value the fail-closed pole uses, so
    // the only difference between the two files is whether an oracle is installed.
    unsafe { std::env::set_var("DREGG_REQUIRE_LEAN", "1") };

    dregg_turn::executor::install_conservation_oracle(Box::new(TestConservationOracle))
        .expect("no oracle should be installed yet in this fresh test process");
    assert!(
        dregg_turn::executor::conservation_oracle_installed(),
        "the conservation oracle must be installed for this pole"
    );
    assert!(
        dregg_turn::executor::ensure_conservation_oracle_installed().is_ok(),
        "with an oracle installed the startup fail-closed check must be satisfied"
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());

    // ── HONEST TURN STILL PASSES ────────────────────────────────────────────────────────────────
    // Same asset X on both legs, +100 / −100. This is the turn the fail-closed pole REFUSES for want
    // of a gate; with a gate present it must settle.
    let (mut ledger, agent_id, x_id, _) = two_asset_ledger();
    let x2 = open_cell(4, [0x11u8; 32], 500);
    let x2_id = x2.id();
    ledger.insert_cell(x2).unwrap();
    {
        let mut agent = ledger.get(&agent_id).unwrap().clone();
        agent.capabilities.grant(x2_id, AuthRequired::None);
        ledger.remove(&agent_id);
        ledger.insert_cell(agent).unwrap();
    }
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.add_action(
        ActionBuilder::new_unchecked_for_tests(x_id, "credit_x", agent_id)
            .with_declared_excess(100)
            .build(),
    );
    builder.add_action(
        ActionBuilder::new_unchecked_for_tests(x2_id, "debit_x", agent_id)
            .with_declared_excess(-100)
            .build(),
    );
    let honest = builder.fee(100).build();

    let result = executor.execute(&honest, &mut ledger);
    assert!(
        !result.is_rejected(),
        "an HONEST, per-asset-conserving turn must be ACCEPTED once a conservation gate is \
         installed — a fail-closed path that also breaks honest turns is not a fix. Got: {result:?}"
    );

    // ── VIOLATING TURN STILL REFUSED, AND AS A CONSERVATION VERDICT ─────────────────────────────
    // The cross-asset teleport: +1M of asset X against a −1M burn of self-issued asset Y. Scalar
    // excess nets to 0; per-asset it does not. The installed gate must NAME the imbalance — this is
    // a conservation VERDICT, not the missing-gate refusal.
    //
    // A FRESH executor: the honest turn above was ACCEPTED, which advanced this executor's receipt
    // chain, and a second turn built with `previous_receipt_hash = None` would be refused with
    // `ReceiptChainMismatch` before conservation is ever consulted. A fresh executor over a fresh
    // ledger keeps this leg's refusal attributable to the conservation gate.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let (mut ledger, agent_id, x_id, y_id) = two_asset_ledger();
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.add_action(
        ActionBuilder::new_unchecked_for_tests(x_id, "mint_x", agent_id)
            .with_declared_excess(1_000_000)
            .build(),
    );
    builder.add_action(
        ActionBuilder::new_unchecked_for_tests(y_id, "burn_y", agent_id)
            .with_declared_excess(-1_000_000)
            .build(),
    );
    let violating = builder.fee(100).build();

    let result = executor.execute(&violating, &mut ledger);
    assert!(
        result.is_rejected(),
        "the cross-asset teleport must be REFUSED with the gate installed, got: {result:?}"
    );
    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::PerAssetConservationViolation { imbalance, .. } => assert!(
            imbalance == 1_000_000 || imbalance == -1_000_000,
            "the per-asset imbalance is the un-conserved residue, got {imbalance}"
        ),
        TurnError::ConservationGateUnavailable => panic!(
            "the gate IS installed, so a refusal must be a conservation VERDICT naming the \
             imbalance — not the missing-gate refusal. The install did not take effect on the \
             decision path."
        ),
        other => panic!("expected PerAssetConservationViolation, got {other:?}"),
    }
    // Atomicity: the refusal rolled everything back.
    assert_eq!(ledger.get(&x_id).unwrap().state.balance(), 0);
    assert_eq!(ledger.get(&y_id).unwrap().state.balance(), 1_000_000);
}
