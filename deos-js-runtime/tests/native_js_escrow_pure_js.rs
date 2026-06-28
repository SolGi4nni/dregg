//! THE PURE-JS 2-PARTY ESCROW, PROVEN BY RUNNING: a single JavaScript program — run in
//! the NATIVE runtime (pure-Rust `boa`, NO servo, NO SpiderMonkey/mozjs) — drives a whole
//! value-coordinating ESCROW across THREE cells: a buyer (`alice`), a seller (`bob`), and
//! the `escrow` coordinator that holds the funds in flight. The app
//!
//!   1. **arms** the escrow with the agreed price through a TYPED method
//!      (`tCell("escrow", "arm", price)`, routed through the escrow's published
//!      [`InterfaceDescriptor`] via the verified DFA `route_method`, `Signature`-gated),
//!   2. **funds** it — `transfer("alice", "escrow", price)` moves the buyer's value into
//!      the escrow, conservation enforced by the executor,
//!   3. **settles** — `tCell("escrow", "settle")` flips the escrow state machine through a
//!      second typed turn, then
//!   4. **pays out** — the payout amount is READ BACK OFF the committed escrow state
//!      (`get("escrow", AMOUNT_SLOT)`) and `transfer("escrow", "bob", owed)` releases it to
//!      the seller.
//!
//! Every effect is a REAL cap-gated verified turn through the embedded executor. This is
//! the second, MORE COMPLEX pure-JS app (after the single-cell kvstore): it coordinates
//! THREE cells, moves value TWICE through an intermediary, drives a typed-method state
//! machine, and reads committed cross-cell state to decide the payout — all with no ambient
//! authority, the app naming cells only by the handles the cap table installed.
//!
//! Proven here:
//!   (a) the happy path SETTLES and CONSERVES — value genuinely moves alice -> escrow ->
//!       bob, and the three-cell balance sum equals the initial sum minus the burned
//!       per-turn fees (no value created or destroyed);
//!   (b) a `reclaim` instead of a settle REFUNDS the depositor — the held value returns to
//!       alice and bob never receives it;
//!   (c) an UNAUTHORIZED release leg is refused IN-BAND — when the app holds only a
//!       `Signature` toward the escrow but the published `settle` method requires the
//!       stronger `Proof`, the settle is refused (`Unauthorized`), the funds stay LOCKED in
//!       the escrow, and nothing reaches bob;
//!   (d) a drain to an UNHELD party is refused IN-BAND — `transfer("escrow", "mallory", ..)`
//!       to a cell the app holds no cap to is `NoCapability`, the escrow funds are untouched,
//!       and a legitimate payout still commits afterward.
//!
//! NAMED HOST-API GAP (the fullest faithful version): each leg of the escrow is its OWN
//! verified turn — the host API exposes no compound/atomic multi-effect turn, so `settle`
//! (the state flip) and the payout `transfer` are two separate receipts, not one atomic
//! "release". Likewise the runtime does not yet enforce the state-machine GUARD (it does not
//! refuse a payout `transfer` unless `state == SETTLED`); the JS program drives the ordering
//! and the cap tooth gates WHO may settle, but the conditional "only-if-funded" link between
//! the state cell and the value move is not yet a single witnessed turn. A conditional /
//! compound-turn host fn (an `Effect::ConditionalBatch`-shaped affordance) is the named
//! next power-up that would make the release atomic and state-guarded.

use deos_js_runtime::applet::{Affordance, ApplyOp};
use deos_js_runtime::{CellWorld, FireError, NativeRuntime};
use dregg_cell::interface::{method_symbol, ArgsSchema, InterfaceDescriptor, MethodSig, Semantics};
use dregg_cell::AuthRequired;

/// Each verified turn the world stamps pays this fee (see `CellWorld::commit`). Fees are
/// burned (they leave the acting cell and are not credited elsewhere), so conservation is
/// "the balance sum drops by exactly one fee per committed turn".
const FEE: i64 = 10_000;

/// The escrow state-machine slot: 0 = OPEN, [`SETTLED`] = released to the seller,
/// [`RECLAIMED`] = refunded to the buyer.
const STATE_SLOT: usize = 1;
/// The slot the agreed price is recorded into by `arm` (witnessed; the payout reads it back).
const AMOUNT_SLOT: usize = 2;
const SETTLED: u64 = 2;
const RECLAIMED: u64 = 3;

/// The escrow's **published typed interface** — the same content-addressed
/// [`InterfaceDescriptor`] a real escrow cell publishes, with `settle_auth` parameterizing
/// the authority the release leg demands (so the unauthorized-release test can publish a
/// stronger `Proof` requirement than the `Signature` the app holds):
///   - `arm(price)`   — `Signature`, `Replayable`: record the agreed price (the deal terms);
///   - `settle()`     — `settle_auth`, `Replayable`: flip the machine to SETTLED (release);
///   - `reclaim()`    — `Signature`, `Replayable`: flip the machine to RECLAIMED (refund);
///   - `status()`     — `None`, `Serviced`: the OFE read seam — refused as a non-turn.
fn escrow_interface(settle_auth: AuthRequired) -> InterfaceDescriptor {
    InterfaceDescriptor::new(vec![
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol("arm"))
        },
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: settle_auth,
            ..MethodSig::replayable(method_symbol("settle"))
        },
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol("reclaim"))
        },
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol("status"))
        },
    ])
}

/// The escrow cell's execution bodies — one [`Affordance`] per typed method name. `arm`
/// records the JS-supplied price into [`AMOUNT_SLOT`] (a literal register-addressed write);
/// `settle`/`reclaim` flip [`STATE_SLOT`] to the terminal state; `status` is the serviced
/// read seam (body present only so the name has an entry — the bridge stops it first).
fn escrow_affordances() -> Vec<Affordance> {
    vec![
        Affordance {
            name: "arm".into(),
            required: AuthRequired::Signature,
            op: ApplyOp::SetSlotFromArg { slot: AMOUNT_SLOT },
        },
        Affordance {
            name: "settle".into(),
            required: AuthRequired::Signature,
            op: ApplyOp::SetSlot {
                slot: STATE_SLOT,
                value: SETTLED,
            },
        },
        Affordance {
            name: "reclaim".into(),
            required: AuthRequired::Signature,
            op: ApplyOp::SetSlot {
                slot: STATE_SLOT,
                value: RECLAIMED,
            },
        },
        Affordance {
            name: "status".into(),
            required: AuthRequired::None,
            op: ApplyOp::SetSlotFromArg { slot: 0 },
        },
    ]
}

/// The starting balance every party is funded with.
const START: i64 = 1_000_000;

/// A three-cell escrow world the JS coordinates:
///   - `alice` — the buyer, the value-bearing HOME cell;
///   - `bob`   — the seller, who is paid on settlement;
///   - `escrow`— the coordinator holding funds in flight, with the published typed
///     interface (`settle` gated on `settle_auth`) and `held_escrow` the authority the app
///     holds toward it.
/// Returns the world plus the three cell ids (for byte-untouched assertions).
fn escrow_world(
    settle_auth: AuthRequired,
    held_escrow: AuthRequired,
) -> (
    CellWorld,
    dregg_types::CellId,
    dregg_types::CellId,
    dregg_types::CellId,
) {
    let mut w = CellWorld::new();

    let mut alice_pk = [0u8; 32];
    alice_pk[0] = 0xA1;
    let alice_id = w.add_cell(
        "alice",
        alice_pk,
        [0u8; 32],
        START,
        &[],
        Vec::new(),
        AuthRequired::Signature,
    );
    w.set_home("alice");

    let mut bob_pk = [0u8; 32];
    bob_pk[0] = 0xB0;
    let bob_id = w.add_cell(
        "bob",
        bob_pk,
        [0u8; 32],
        START,
        &[],
        Vec::new(),
        AuthRequired::Signature,
    );

    let mut escrow_pk = [0u8; 32];
    escrow_pk[0] = 0xE5;
    let escrow_id = w.add_cell(
        "escrow",
        escrow_pk,
        [0u8; 32],
        START,
        &[(STATE_SLOT, 0u64), (AMOUNT_SLOT, 0u64)],
        escrow_affordances(),
        held_escrow,
    );
    w.publish_interface("escrow", escrow_interface(settle_auth));

    (w, alice_id, bob_id, escrow_id)
}

/// The sum of the three parties' balances — the conserved quantity. Each committed turn
/// burns exactly one [`FEE`] from the acting cell, so this sum equals the initial
/// `3 * START` minus `FEE * receipts`.
fn balance_sum(w: &CellWorld) -> i64 {
    w.balance("alice").unwrap() + w.balance("bob").unwrap() + w.balance("escrow").unwrap()
}

/// (a) THE HAPPY PATH: one pure-JS program arms, funds, settles, and pays out the escrow.
/// Value genuinely moves alice -> escrow -> bob, the typed-method state machine reaches
/// SETTLED, and the three-cell balance sum is conserved (initial sum minus the burned fees).
#[test]
fn pure_js_escrow_happy_path_settles_and_conserves() {
    let (world, _a, _b, _e) = escrow_world(AuthRequired::Signature, AuthRequired::Signature);
    let initial_sum = balance_sum(&world);
    assert_eq!(initial_sum, 3 * START, "three parties funded at START each");

    // The whole 2-party escrow as PURE JS-on-cells. The price is named once; the escrow is
    // armed with it (typed turn), funded by the buyer (conserved transfer), settled (typed
    // turn), and the payout amount is READ BACK off committed escrow state to drive the
    // release transfer to the seller.
    let app = format!(
        r#"
        var price = 250000;

        // 1. arm the escrow with the agreed price — a Signature-gated typed-method turn
        //    routed through the escrow's published interface (records price -> AMOUNT_SLOT).
        tCell("escrow", "arm", price);

        // 2. the buyer funds the escrow — a conserved Transfer turn (alice -> escrow).
        transfer("alice", "escrow", price);

        // 3. settle — flip the escrow state machine to SETTLED (a second typed turn).
        tCell("escrow", "settle");

        // 4. read the agreed amount back OFF committed escrow state, then release it to the
        //    seller (escrow -> bob). The payout is driven by witnessed cross-cell state.
        var owed = get("escrow", {amount_slot});
        transfer("escrow", "bob", owed);

        // the script's result: the amount released to the seller.
        owed;
    "#,
        amount_slot = AMOUNT_SLOT
    );

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &app)
        .expect("the pure-JS escrow app runs natively");
    let w = &outcome.world;

    assert!(
        outcome.last_fire_error.is_none(),
        "every coordinated escrow effect committed cleanly: {:?}",
        outcome.last_fire_error
    );

    // The escrow recorded the agreed price and reached the SETTLED terminal state.
    assert_eq!(
        w.get_slot("escrow", AMOUNT_SLOT).unwrap(),
        250_000,
        "arm recorded the agreed price into committed escrow state"
    );
    assert_eq!(
        w.get_slot("escrow", STATE_SLOT).unwrap(),
        SETTLED,
        "the settle typed-method turn flipped the escrow state machine to SETTLED"
    );

    // FOUR verified turns committed: arm, fund-transfer, settle, payout-transfer.
    assert_eq!(
        w.receipts().len(),
        4,
        "four coordinated verified turns (arm, fund, settle, payout) left four receipts"
    );

    // VALUE GENUINELY MOVED, and is CONSERVED:
    //   alice (buyer): START - FEE (her fund-transfer turn) - price (sent into escrow).
    //   bob   (seller): START + price (received on payout).
    //   escrow: START - 3*FEE (arm, settle, payout turns) + price - price (in then out).
    assert_eq!(
        w.balance("alice").unwrap(),
        START - FEE - 250_000,
        "buyer paid her fund-transfer fee and parted with the price"
    );
    assert_eq!(
        w.balance("bob").unwrap(),
        START + 250_000,
        "seller received exactly the price — value reached the counterparty"
    );
    assert_eq!(
        w.balance("escrow").unwrap(),
        START - 3 * FEE,
        "the escrow netted to zero on value (in then out), paying only its three turn fees"
    );

    // CONSERVATION: the three-cell sum dropped by exactly one fee per committed turn — no
    // value was created or destroyed in the coordination, only the per-turn fees burned.
    assert_eq!(
        balance_sum(w),
        initial_sum - FEE * w.receipts().len() as i64,
        "balance conserved: initial sum minus the burned per-turn fees"
    );
}

/// (b) THE RECLAIM PATH: instead of settling, the escrow is reclaimed — the held value is
/// REFUNDED to the depositor (alice) and the seller (bob) never receives it.
#[test]
fn pure_js_escrow_reclaim_refunds_the_depositor() {
    let (world, _a, _b, _e) = escrow_world(AuthRequired::Signature, AuthRequired::Signature);
    let initial_sum = balance_sum(&world);

    let app = format!(
        r#"
        var price = 250000;
        tCell("escrow", "arm", price);        // record the deal
        transfer("alice", "escrow", price);   // buyer funds the escrow
        tCell("escrow", "reclaim");           // dispute / timeout: reclaim instead of settle
        var owed = get("escrow", {amount_slot});
        transfer("escrow", "alice", owed);    // refund the buyer
    "#,
        amount_slot = AMOUNT_SLOT
    );

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &app)
        .expect("the pure-JS escrow reclaim app runs natively");
    let w = &outcome.world;

    assert!(
        outcome.last_fire_error.is_none(),
        "reclaim path committed cleanly"
    );
    assert_eq!(
        w.get_slot("escrow", STATE_SLOT).unwrap(),
        RECLAIMED,
        "the escrow reached the RECLAIMED terminal state"
    );

    // The buyer is made whole minus only her transfer fee; the seller got NOTHING.
    assert_eq!(
        w.balance("alice").unwrap(),
        START - FEE,
        "buyer was refunded — out only her single fund-transfer fee"
    );
    assert_eq!(
        w.balance("bob").unwrap(),
        START,
        "seller received nothing on a reclaim"
    );
    assert_eq!(
        balance_sum(w),
        initial_sum - FEE * w.receipts().len() as i64,
        "balance conserved across the reclaim flow"
    );
}

/// (c) THE UNAUTHORIZED-RELEASE PROOF: the app holds only a `Signature` toward the escrow,
/// but the PUBLISHED `settle` method requires the stronger, incomparable `Proof`. The arm
/// and the fund succeed, but the settle is refused IN-BAND (`Unauthorized`, via the same
/// `is_attenuation` tooth, gated on the PUBLISHED interface) — the funds stay LOCKED in the
/// escrow and never reach the seller.
#[test]
fn pure_js_escrow_unauthorized_settle_keeps_funds_locked() {
    // settle requires Proof; the app holds only Signature toward the escrow.
    let (world, _a, _b, _e) = escrow_world(AuthRequired::Proof, AuthRequired::Signature);

    let app = format!(
        r#"
        var price = 250000;
        tCell("escrow", "arm", price);        // OK — arm requires Signature
        transfer("alice", "escrow", price);   // OK — buyer funds the escrow
        try {{
            tCell("escrow", "settle");        // REFUSED — settle requires Proof, app holds Signature
            transfer("escrow", "bob", price); // unreachable: the throw above skips this
        }} catch (e) {{ /* the unauthorized release threw; nothing reached bob */ }}
        get("escrow", {amount_slot});
    "#,
        amount_slot = AMOUNT_SLOT
    );

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &app)
        .expect("the try/catch swallows the unauthorized-settle throw");
    let w = &outcome.world;

    // The release leg was refused on the PUBLISHED cap requirement.
    assert!(
        matches!(outcome.last_fire_error, Some(FireError::Unauthorized(_))),
        "the unauthorized settle recorded an Unauthorized refusal, got {:?}",
        outcome.last_fire_error
    );

    // The escrow is still OPEN and STILL HOLDS the funds — nothing was released.
    assert_eq!(
        w.get_slot("escrow", STATE_SLOT).unwrap(),
        0,
        "the escrow state machine never left OPEN (settle was refused)"
    );
    assert_eq!(
        w.balance("escrow").unwrap(),
        START - FEE + 250_000,
        "the escrow STILL HOLDS the funded price (paid only its arm-turn fee)"
    );
    assert_eq!(
        w.balance("bob").unwrap(),
        START,
        "the seller got nothing — the unauthorized release moved no value"
    );

    // Only the arm + fund committed; the settle and its payout did not.
    assert_eq!(
        w.receipts().len(),
        2,
        "exactly arm + fund committed; the refused settle and its payout did not"
    );
}

/// (d) THE CONFINEMENT PROOF: the app cannot drain the escrow to a party it holds no cap
/// to. `transfer("escrow", "mallory", ..)` names a cell absent from the cap table —
/// `NoCapability`, the ocap stance (you cannot even name what you do not hold). The escrow
/// funds are untouched, the uncapped `mallory` cell stays byte-identical, and a LEGITIMATE
/// payout still commits after the refused drain.
#[test]
fn pure_js_escrow_cannot_drain_to_an_uncapped_party() {
    let (mut world, _a, _b, _e) = escrow_world(AuthRequired::Signature, AuthRequired::Signature);
    // mallory exists on the SAME ledger but the app holds NO cap to it (no handle).
    let mut mallory_pk = [0u8; 32];
    mallory_pk[0] = 0x4D;
    let mallory_id = world.add_uncapped_cell(mallory_pk, [0u8; 32], 500, &[(0usize, 77u64)]);
    let initial_sum = balance_sum(&world);

    let app = r#"
        var price = 250000;
        tCell("escrow", "arm", price);
        transfer("alice", "escrow", price);
        tCell("escrow", "settle");
        try {
            // a drain to a cell the app holds no cap to — unreachable, refused in-band.
            transfer("escrow", "mallory", price);
        } catch (e) { /* NoCapability: the escrow is never touched by this */ }
        // the LEGITIMATE payout still commits after the refused drain.
        transfer("escrow", "bob", price);
    "#;

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, app)
        .expect("the try/catch swallows the drain over-reach");
    let w = &outcome.world;

    // The drain was recorded as a missing capability — the ocap gate bit.
    assert!(
        matches!(outcome.last_fire_error, Some(FireError::NoCapability(_))),
        "the drain to an unheld cell recorded a NoCapability refusal, got {:?}",
        outcome.last_fire_error
    );

    // mallory on the ledger is byte-untouched: same balance, same field.
    let mallory = w.cell_on_ledger(mallory_id).expect("mallory on the ledger");
    assert_eq!(
        mallory.state.balance(),
        500,
        "uncapped mallory balance untouched"
    );
    assert_eq!(
        mallory.state.get_field(0).copied().map(|fe| fe[0]),
        Some(77),
        "uncapped mallory field untouched — the drain never reached it"
    );

    // The LEGITIMATE payout still moved the value to the seller.
    assert_eq!(
        w.balance("bob").unwrap(),
        START + 250_000,
        "the legitimate payout still committed after the refused drain"
    );
    // arm, fund, settle, legit-payout = 4 turns; the refused drain committed none.
    assert_eq!(
        w.receipts().len(),
        4,
        "only the four legitimate turns committed; the drain committed nothing"
    );
    // Conservation holds across the three deal parties (`balance_sum` already excludes the
    // uncapped mallory — it is not in the deal and stayed byte-untouched above).
    assert_eq!(
        balance_sum(w),
        initial_sum - FEE * w.receipts().len() as i64,
        "balance conserved across the three deal parties (mallory excluded)"
    );
}
