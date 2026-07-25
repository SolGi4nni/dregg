//! REALITY GATE: with NO verified conservation gate installed, the executor REFUSES rather than
//! deciding the ASSET-INFLATION boundary with the hand-written Rust `BlockConservation` twin.
//!
//! ## What was open
//!
//! `TurnExecutor::check_per_asset_conservation_by_asset` routes the per-asset `Σδ=0` decision
//! through the verified, Lean-authored `dregg_cross_cell_conserves`
//! (`Dregg2.Circuit.CrossCellConserveDecision.conservesFFI`, proved equal to the committed
//! `CrossCellConservation` AIR boundary by
//! `CrossCellConserveRefine.decision_conserves_iff_air_boundary`) — when a `ConservationOracle` is
//! installed. When one was NOT, it FELL THROUGH to the Rust `BlockConservation` collector **on
//! native**, not merely on the wasm32 / zkVM guest where no archive can exist. So a stale or absent
//! `libdregg_lean.a` silently returned a deployed node to the unverified decider — the twin that
//! already drifted once into the asset-blind inflation CRITICAL — with only a build WARNING to say
//! so. The `lean-twins.tsv` `route` row greps for the SYMBOL `dregg_cross_cell_conserves` inside
//! `atomic.rs` and passed the whole time: a name-whitelist cannot see a fallthrough.
//!
//! ## What this test pins
//!
//! With no oracle installed and the verified gate DEMANDED, a conservation-VIOLATING turn is refused
//! with [`TurnError::ConservationGateUnavailable`] — **not** `PerAssetConservationViolation`. The
//! distinction is the whole point: `PerAssetConservationViolation` would mean the Rust twin ran and
//! answered. `ConservationGateUnavailable` means nothing entitled to answer was present, so nothing
//! answered.
//!
//! And the fail-closed disposition is TOTAL: an HONEST, exactly-conserving turn is refused too. That
//! is the correct posture (a node that cannot verify conservation must not settle value) and it is
//! why the other pole, `conservation_oracle_installed_poles.rs`, exists — a fail-closed path that
//! also breaks honest turns forever is not a fix, so that file shows the honest turn passing the
//! moment the gate IS present.
//!
//! ## Why this file is its own test binary, and why it sets `DREGG_REQUIRE_LEAN=1`
//!
//! The oracle lives in a process-wide `OnceLock`, so the no-oracle pole must be a process where no
//! oracle is ever installed — a separate integration-test binary, not a `#[test]` beside one that
//! installs one.
//!
//! On a native RELEASE build the refusal is a COMPILE-TIME fact: `unverified_rust_conservation_fallback`
//! is `#[cfg(not(all(any(unix, windows), not(debug_assertions))))]`, so it does not exist in a
//! deployed node's binary at all. `cargo test` is a DEBUG build, where the labeled fallback IS
//! compiled (the whole workspace's debug test suite can never link the archive and still needs the
//! arithmetic). `DREGG_REQUIRE_LEAN=1` — the tree's existing "I demand the verified artifact" signal
//! — promotes that build's no-oracle path to the same hard refusal, which is what lets this gate run
//! in a normal `cargo test` instead of only under `--release`.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{ActionBuilder, ComputronCosts, TurnBuilder, TurnError, TurnExecutor};

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

/// A ledger holding an agent (with capabilities over both targets) and two cells of DISTINCT asset
/// classes. Returns `(ledger, agent, cell_x, cell_y)`.
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

/// THE FAIL-CLOSED GATE. No conservation oracle in this process; the verified gate is demanded.
///
/// One `#[test]` per binary on purpose: it mutates the process environment, and with a single test
/// there is no other thread to race (see the `SAFETY` note below).
#[test]
fn conservation_fails_closed_without_gate() {
    // SAFETY: this test binary contains exactly one `#[test]`, so no other thread is reading or
    // writing the environment while this runs. The variable is read (not cached) on each
    // conservation decision by `conservation_oracle::require_verified_conservation_gate`.
    unsafe { std::env::set_var("DREGG_REQUIRE_LEAN", "1") };

    // Ground truth: no oracle is installed and none can be. `dregg-turn`'s own test binaries never
    // link `libdregg_lean.a` (that is `dregg-exec-lean`'s job, and it depends on `dregg-turn`), so
    // this process IS the "missing Lean archive" state on a native build.
    assert!(
        !dregg_turn::executor::conservation_oracle_installed(),
        "dregg-turn's integration-test binary cannot link libdregg_lean.a — no conservation oracle \
         should be installed. If one is, this test is not exercising the no-gate pole."
    );
    assert!(
        dregg_turn::executor::ensure_conservation_oracle_installed().is_err(),
        "a native build with no conservation oracle must report the gate as MISSING"
    );
    assert!(
        dregg_turn::executor::require_verified_conservation_gate(),
        "DREGG_REQUIRE_LEAN=1 must demand the verified conservation gate"
    );

    // ── POLE 1: a conservation-VIOLATING turn is REFUSED, and refused BY THE GATE ──────────────
    // The cross-asset teleport that the asset-blind twin once accepted: +1M of asset X against a
    // −1M burn of self-issued asset Y. The scalar `excess` nets to 0; per-asset it does not.
    let (mut ledger, agent_id, x_id, y_id) = two_asset_ledger();
    let executor = TurnExecutor::new(ComputronCosts::zero());
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
        "a conservation-violating turn must be REFUSED with no verified gate, got: {result:?}"
    );
    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::ConservationGateUnavailable => { /* the gate refused: nothing decided it */ }
        TurnError::PerAssetConservationViolation { asset, imbalance } => panic!(
            "FAIL-OPEN: the turn was refused by the UNVERIFIED Rust BlockConservation twin \
             (asset {asset}, imbalance {imbalance}), not by the fail-closed gate. The Rust twin is \
             answering the asset-inflation question with no verified gate installed — the exact \
             defect this test exists to prevent."
        ),
        other => panic!("expected ConservationGateUnavailable, got {other:?}"),
    }
    // Atomicity: the refusal rolled everything back.
    assert_eq!(ledger.get(&x_id).unwrap().state.balance(), 0);
    assert_eq!(ledger.get(&y_id).unwrap().state.balance(), 1_000_000);

    // ── POLE 2: the refusal is TOTAL — an HONEST, exactly-conserving turn is refused too ───────
    // A node with no verified conservation gate must not settle value at all. `_poles.rs` shows the
    // same honest turn ACCEPTED the moment a gate is installed, so this is a missing-gate refusal
    // and not a broken conservation check.
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
    // Same asset X on both legs, +100 / −100: conserves per-asset AND in scalar.
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
        result.is_rejected(),
        "an honest turn must ALSO be refused with no verified conservation gate — the fail-closed \
         disposition is total. An accept here means some path still decides conservation without \
         the verified gate. Got: {result:?}"
    );
    let (error, _) = result.unwrap_rejected();
    assert!(
        matches!(error, TurnError::ConservationGateUnavailable),
        "the honest turn's refusal must be the MISSING-GATE refusal, not a conservation verdict \
         (which would mean the unverified twin ran); got {error:?}"
    );
}
