//! # Durable execution as a payable resource — the provider, end to end.
//!
//! The prototype flow of a fly.io-lite / cloudflare-lite durable-execution
//! provider, proven on dregg-native primitives with NO new kernel effect:
//!
//!   1. **Lease** — a provider offers a durable-execution slot; an agent opens a
//!      lease cell whose committed umem heap holds the durable execution image
//!      (a genesis checkpoint), with a sealed rent schedule (the meter).
//!   2. **Meter + pay per period** — each period the rent obligation is discharged
//!      ONCE, on-schedule, for the exact rent (the recurring forge-detectors bite),
//!      and a real conserving `Transfer` moves the rent from the lease to the
//!      provider (per-asset Σδ=0 holds across the lease).
//!   3. **Durable state advances** — the provider delivers: the lease's durable
//!      checkpoint cursor moves forward (the executor re-enforces `Monotonic(STEP)`,
//!      so a rewound cursor is a REAL refusal), and the working memory survives in
//!      the committed, witnessed, passable umem heap image.
//!   4. **Lapse on non-payment** — when a rent period goes undischarged, the
//!      schedule audit lapses the lease and durable execution stops (the slot is
//!      reclaimed).
//!
//! Conservation (Σ CREDIT = 0) is asserted across the whole flow: leasing durable
//! execution MOVES real value but never creates or destroys it.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, Effect, EmbeddedExecutor, InvokeAuthority,
    StarbridgeAppContext,
};
use dregg_cell::{Cell, CellId, EFFECT_MINT, Permissions};

use starbridge_execution_lease::{
    LeaseError, LeaseTerms, WORKING_BASE, advance_checkpoint, checkpoint_step, field_from_u64,
    fire_advance, heap_checkpoint_step, is_lapsed, lapse_if_behind, lease_app, lease_cell_program,
    meter_period, open_lease, pay_rent, periods_paid, seed_lease, working_memory,
};

/// The shared credit asset every value cell denominates in (its `token_id`).
const CREDIT: [u8; 32] = [0xCDu8; 32];
/// The rent per period.
const RENT: u64 = 100;
/// The prepaid balance the agent funds the lease cell with (3 periods).
const PREPAID: u64 = 300;

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

fn credit_cell(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let mut cell = Cell::with_balance(pk, CREDIT, 0);
    cell.permissions = open_permissions();
    cell
}

fn derived_well_id(token_id: &[u8; 32]) -> CellId {
    let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", token_id);
    CellId::derive_raw(&well_pubkey, token_id)
}

fn per_asset_supply(exec: &EmbeddedExecutor, asset: &[u8; 32]) -> i128 {
    exec.with_ledger_mut(|ledger| {
        ledger
            .iter()
            .filter(|(_, c)| c.token_id() == asset)
            .map(|(_, c)| c.state.balance() as i128)
            .sum()
    })
}

fn balance_of(exec: &EmbeddedExecutor, cell: CellId) -> i64 {
    exec.with_ledger_mut(|ledger| ledger.get(&cell).map(|c| c.state.balance()).unwrap_or(0))
}

#[test]
fn durable_execution_lease_meters_pays_advances_and_lapses_conserving() {
    // ── One World: the operator is the provider's minter + the agent's controller. ──
    let operator = AppCipherclerk::new(AgentCipherclerk::new(), [0x42u8; 32]);
    let exec = EmbeddedExecutor::new(&operator, "default");
    let operator_cell = operator.cell_id();

    // ── The provider's slot owner cell + the agent's lease cell (its durable slot). ──
    let provider = credit_cell(1);
    let lease = credit_cell(2);
    let provider_id = provider.id();
    let lease_id = lease.id();
    exec.ensure_cell(provider).expect("provider co-placed");
    exec.ensure_cell(lease).expect("lease co-placed");

    let well_id = derived_well_id(&CREDIT);
    let asset_cid = CellId::from_bytes(CREDIT);

    // ── Grant the operator MINT authority over CREDIT + access to the cells. ──
    exec.with_ledger_mut(|ledger| {
        let op = ledger
            .get_mut(&operator_cell)
            .expect("operator cell exists");
        op.capabilities
            .grant_faceted(well_id, AuthRequired::None, EFFECT_MINT)
            .expect("grant mint-cap over CREDIT well");
        op.capabilities
            .grant(lease_id, AuthRequired::None)
            .expect("grant lease access");
        op.capabilities
            .grant(provider_id, AuthRequired::None)
            .expect("grant provider access");
    });

    // ── The agent funds the lease cell with a prepaid balance (a mint conserves). ──
    let mint = operator.make_action(
        lease_id,
        "fund_lease",
        vec![Effect::Mint {
            target: lease_id,
            slot: 0,
            amount: PREPAID,
        }],
    );
    exec.submit_action(&operator, mint).expect("fund the lease");
    assert_eq!(balance_of(&exec, lease_id), PREPAID as i64);
    assert_eq!(
        per_asset_supply(&exec, &CREDIT),
        0,
        "Σ CREDIT = 0 after funding"
    );

    // ── (1) OPEN the lease: install the life-of-lease program + seal the rent
    //        schedule (the meter) + the genesis durable checkpoint. ──
    let terms = LeaseTerms::new(provider_id, lease_id, asset_cid, RENT, 50, 1000, 0);
    exec.install_program(lease_id, lease_cell_program());
    exec.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&lease_id).expect("lease cell");
        open_lease(cell, &terms, field_from_u64(0x6E_0000)).expect("open the lease");
    });
    assert_eq!(
        checkpoint_step_live(&exec, lease_id),
        0,
        "genesis checkpoint"
    );

    // ── (2) + (3): two metered+paid periods, each delivering a durable advance. ──
    for (period, clock, digest, work) in [
        (0i64, 1000i64, 0x11u64, 0xCAFEu64),
        (1i64, 1050i64, 0x22u64, 0xF00Du64),
    ] {
        // METER: discharge exactly the rent for this period (forge-detectors bite).
        let moved = exec.with_ledger_mut(|ledger| {
            let cell = ledger.get_mut(&lease_id).expect("lease cell");
            meter_period(cell, &terms, period, clock)
        });
        assert_eq!(
            moved,
            Ok(RENT),
            "metered the exact rent for period {period}"
        );

        // PAY: a real conserving Transfer of the rent from the lease to the provider.
        let pay = pay_rent(&operator, &terms, InvokeAuthority::Signature)
            .expect("rent pays through the Payable interface");
        let provider_before = balance_of(&exec, provider_id);
        exec.submit_turn(&pay).expect("the rent Transfer commits");
        assert_eq!(
            balance_of(&exec, provider_id),
            provider_before + RENT as i64,
            "the provider received the rent"
        );
        assert_eq!(
            per_asset_supply(&exec, &CREDIT),
            0,
            "Σ CREDIT = 0 after paying rent"
        );

        // DELIVER: the provider advances the durable checkpoint. The executor
        // re-enforces Monotonic(STEP) — and the umem heap image survives + advances.
        let commit_before = lease_commitment(&exec, lease_id);
        let live = exec.cell_state(lease_id).expect("lease state");
        let next_step = live.fields[0]; // STEP_SLOT
        let next = u64_of(&next_step) + 1;
        let advance = starbridge_execution_lease::service::LeaseService::new(lease_id)
            .advance(
                &operator,
                next,
                field_from_u64(digest),
                InvokeAuthority::Signature,
            )
            .expect("advance routes through the interface");
        exec.submit_turn(&advance)
            .expect("the durable checkpoint advances");
        // Mirror the executor-enforced cursor into the committed umem heap + write
        // the running execution's working memory.
        exec.with_ledger_mut(|ledger| {
            let cell = ledger.get_mut(&lease_id).expect("lease cell");
            starbridge_execution_lease::mirror_checkpoint(
                cell,
                &[(WORKING_BASE, field_from_u64(work))],
            );
        });
        assert_eq!(
            checkpoint_step_live(&exec, lease_id),
            next,
            "durable cursor advanced"
        );
        let cell = exec.with_ledger_mut(|l| l.get(&lease_id).cloned()).unwrap();
        assert_eq!(
            heap_checkpoint_step(&cell),
            next as i64,
            "umem heap mirrors the cursor"
        );
        assert_eq!(
            working_memory(&cell, WORKING_BASE),
            Some(field_from_u64(work)),
            "the durable working memory survives in the committed image"
        );
        assert_ne!(
            commit_before,
            lease_commitment(&exec, lease_id),
            "the checkpoint advance is witnessed (the commitment moves)"
        );
    }

    // The durable cursor is FORWARD-ONLY: a rewind is a real executor refusal.
    let rewind = starbridge_execution_lease::service::LeaseService::new(lease_id)
        .advance(
            &operator,
            0,
            field_from_u64(0xDEAD),
            InvokeAuthority::Signature,
        )
        .expect("the rewind turn builds");
    assert!(
        exec.submit_turn(&rewind).is_err(),
        "a durable-cursor rewind is refused"
    );
    assert_eq!(
        checkpoint_step_live(&exec, lease_id),
        2,
        "the cursor is unchanged by the refused rewind"
    );

    // ── (4) LAPSE on non-payment: skip period 2, let the clock run past its due
    //        block — the schedule audit lapses the lease, and execution stops. ──
    let lapsed = exec.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&lease_id).expect("lease cell");
        lapse_if_behind(cell, &terms, 1100)
    });
    assert_eq!(lapsed, Ok(true), "an unpaid period lapses the lease");
    let cell = exec.with_ledger_mut(|l| l.get(&lease_id).cloned()).unwrap();
    assert!(is_lapsed(&cell), "the lease is lapsed");

    // A lapsed lease cannot advance its durable execution (slot reclaimed).
    let blocked = exec.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&lease_id).expect("lease cell");
        advance_checkpoint(cell, field_from_u64(0x99), &[])
    });
    assert_eq!(
        blocked,
        Err(LeaseError::Lapsed),
        "durable execution stops on lapse"
    );

    // ── Conservation + accounting across the whole lease. ──
    assert_eq!(periods_paid(&cell), 2, "two periods were metered+paid");
    assert_eq!(
        balance_of(&exec, provider_id),
        2 * RENT as i64,
        "provider earned two periods' rent"
    );
    assert_eq!(
        balance_of(&exec, lease_id),
        (PREPAID - 2 * RENT) as i64,
        "the lease spent its rent"
    );
    assert_eq!(
        per_asset_supply(&exec, &CREDIT),
        0,
        "Σ CREDIT = 0 across the whole lease"
    );
}

/// The deos surface: the gated `advance` fire delivers a durable checkpoint while
/// the lease is LIVE, and goes DARK (refused in-band) once the lease has lapsed —
/// the not-lapsed precondition is the slot-reclaim gate.
#[test]
fn deos_advance_fire_is_gated_on_a_live_lease() {
    let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [7u8; 32]);
    let exec = EmbeddedExecutor::new(&cipherclerk, "default");
    let _ctx = StarbridgeAppContext::new(cipherclerk.clone(), exec.clone());

    let lease_id = exec.cell_id();
    let terms = LeaseTerms::new(
        CellId::from_bytes([0xABu8; 32]),
        lease_id,
        lease_id,
        RENT,
        50,
        1000,
        0,
    );
    seed_lease(&exec, &terms, field_from_u64(1));
    let app = lease_app(&cipherclerk, &exec);

    // LIVE lease: the gated advance fire delivers a checkpoint.
    fire_advance(
        &app,
        &AuthRequired::Signature,
        &cipherclerk,
        &exec,
        field_from_u64(2),
        vec![(WORKING_BASE, field_from_u64(0xABCD))],
    )
    .expect("a live lease delivers a durable checkpoint");
    assert_eq!(checkpoint_step_live(&exec, lease_id), 1);
    let cell = exec.with_ledger_mut(|l| l.get(&lease_id).cloned()).unwrap();
    assert_eq!(
        working_memory(&cell, WORKING_BASE),
        Some(field_from_u64(0xABCD))
    );

    // Lapse the lease, then the gated advance fire goes DARK (refused in-band).
    exec.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&lease_id).expect("lease cell");
        cell.state.set_field(2, field_from_u64(1)); // LAPSED_SLOT
    });
    assert!(
        fire_advance(
            &app,
            &AuthRequired::Signature,
            &cipherclerk,
            &exec,
            field_from_u64(3),
            vec![],
        )
        .is_err(),
        "a lapsed lease's advance is refused by the not-lapsed precondition"
    );
    assert_eq!(
        checkpoint_step_live(&exec, lease_id),
        1,
        "no checkpoint after lapse"
    );
}

// ── helpers ────────────────────────────────────────────────────────────────────

fn u64_of(f: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

fn checkpoint_step_live(exec: &EmbeddedExecutor, lease: CellId) -> u64 {
    let cell = exec.with_ledger_mut(|l| l.get(&lease).cloned()).unwrap();
    checkpoint_step(&cell)
}

fn lease_commitment(exec: &EmbeddedExecutor, lease: CellId) -> [u8; 32] {
    let cell = exec.with_ledger_mut(|l| l.get(&lease).cloned()).unwrap();
    cell.state_commitment()
}
