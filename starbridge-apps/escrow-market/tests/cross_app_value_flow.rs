//! # The FIRST cross-app token VALUE FLOW — proven end to end.
//!
//! The interop census (`docs/deos/APPS-INTEROP-CENSUS.md`) found that NO value
//! flows between starbridge-apps: every app models money as scalar `SetField`s on
//! its own cell, never as a movable conserved asset crossing an app boundary
//! (0 `Effect::Transfer`/`Mint`/`Burn` in the whole gallery). This test closes the
//! keystone gap — value flowing ACROSS two apps, conservation-respecting, with NO
//! kernel change — by walking the census's "cleanest first interop win":
//!
//!   1. **Mint** a shared credit asset on a treasury cell (`Effect::Mint`, the
//!      cap-gated supply entry) — the bounty board's reward is now a CONSERVED
//!      credit, not a scalar field.
//!   2. **Co-place** `bounty-board` + `escrow-market` value cells on ONE `World`
//!      / ledger (the shared `EmbeddedExecutor`).
//!   3. **Bounty payout** fires a REAL `Effect::Transfer` of that credit from the
//!      bounty treasury INTO the escrow-market escrow cell — crossing the app
//!      boundary — THROUGH the shared `Payable` interface.
//!   4. **Escrow settles onward**: the escrow releases the held credit to the
//!      payee with another `Effect::Transfer`, again through `Payable`.
//!   5. **Assert per-asset Σδ=0 across the WHOLE World** — the kernel conservation
//!      invariant (`Σ holders(asset) + well(asset) = 0`) holds ACROSS the app
//!      boundary, which is the thing that did not exist before.
//!
//! The substrate is entirely pre-existing: the Σδ=0 executor, `Effect::Transfer`,
//! `Effect::Mint`, `AssetId := issuer-cell`, the shared `World`. This is pure
//! wiring — two apps both implementing the `Payable` DSI and transacting over it.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, Effect, EmbeddedExecutor, InvokeAuthority, payable_descriptor,
};
use dregg_cell::interface::method_symbol;
use dregg_cell::{AuthRequired, Cell, CellId, EFFECT_MINT, Permissions};

use starbridge_bounty_board::BountyTreasury;
use starbridge_escrow_market::EscrowVault;

/// The shared credit asset every value cell denominates in (its `token_id`). The
/// asset IS its issuer-cell (`AssetId := issuer-cell`); the per-asset Σδ=0 holds
/// over exactly the cells carrying this `token_id` plus the asset's issuer well.
const CREDIT: [u8; 32] = [0xCDu8; 32];

/// The reward that flows bounty-treasury → escrow → payee.
const REWARD: u64 = 2_500;

/// Fully-open permissions — these are wallet/holder cells (the value flows by the
/// EFFECT-level gates: the mint-authority cap and the cross-cell move, not the
/// holder's own permission tier).
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

/// A credit-asset holder cell (`token_id == CREDIT`), open, starting at zero.
fn credit_cell(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let mut cell = Cell::with_balance(pk, CREDIT, 0);
    cell.permissions = open_permissions();
    cell
}

/// The deterministic per-asset issuer well id (mirrors the executor's
/// `derive_issuer_well`): the −supply account that makes a mint conserve.
fn derived_well_id(token_id: &[u8; 32]) -> CellId {
    let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", token_id);
    CellId::derive_raw(&well_pubkey, token_id)
}

/// Sum the balances of every cell denominating in `asset` (the per-asset supply).
/// For a conserving asset this is identically 0: `Σ holders + well = 0`.
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
fn value_flows_across_two_apps_and_conservation_holds() {
    // ── One World, one ledger: the shared EmbeddedExecutor. The operator is the
    //    minter / central treasury authority (its own agent cell, a DIFFERENT asset
    //    than CREDIT, funded for fees — so it never pollutes the CREDIT supply). ──
    let operator = AppCipherclerk::new(AgentCipherclerk::new(), [0x42u8; 32]);
    let exec = EmbeddedExecutor::new(&operator, "default");
    let operator_cell = operator.cell_id();

    // ── Co-place the two apps' value cells on the one World. All CREDIT holders. ──
    let treasury = credit_cell(1); // bounty-board's reward treasury
    let escrow = credit_cell(2); // escrow-market's escrow holding vault
    let payee = credit_cell(3); // the worker who is ultimately paid
    let treasury_id = treasury.id();
    let escrow_id = escrow.id();
    let payee_id = payee.id();
    exec.ensure_cell(treasury).expect("treasury co-placed");
    exec.ensure_cell(escrow).expect("escrow co-placed");
    exec.ensure_cell(payee).expect("payee co-placed");

    let well_id = derived_well_id(&CREDIT);

    // ── Grant the operator MINT authority over the CREDIT well (control-grade cap
    //    carrying the EFFECT_MINT facet — the Rust image of Lean `mintAuthorizedB`)
    //    plus access to the cells it will act on. ──
    exec.with_ledger_mut(|ledger| {
        let op = ledger
            .get_mut(&operator_cell)
            .expect("operator cell exists");
        op.capabilities
            .grant_faceted(well_id, AuthRequired::None, EFFECT_MINT)
            .expect("grant mint-cap over the CREDIT well");
        op.capabilities
            .grant(treasury_id, AuthRequired::None)
            .expect("grant treasury access");
        op.capabilities
            .grant(escrow_id, AuthRequired::None)
            .expect("grant escrow access");
    });

    // Sanity: before minting, the CREDIT asset has no supply at all.
    assert_eq!(
        per_asset_supply(&exec, &CREDIT),
        0,
        "no CREDIT exists before the mint"
    );

    // ── (1) MINT the shared credit onto the bounty treasury (the cap-gated supply
    //        entry). The well goes −REWARD, the treasury +REWARD: a mint CONSERVES. ──
    let mint = operator.make_action(
        treasury_id,
        "mint_reward",
        vec![Effect::Mint {
            target: treasury_id,
            slot: 0,
            amount: REWARD,
        }],
    );
    exec.submit_action(&operator, mint)
        .expect("cap-gated mint commits");

    assert_eq!(
        balance_of(&exec, treasury_id),
        REWARD as i64,
        "the treasury holds the minted reward"
    );
    assert_eq!(
        balance_of(&exec, well_id),
        -(REWARD as i64),
        "the CREDIT well carries the −supply"
    );
    assert_eq!(
        per_asset_supply(&exec, &CREDIT),
        0,
        "per-asset Σδ=0 after the mint (Σ holders + well = 0)"
    );

    // ── (2) BOUNTY PAYOUT crosses the app boundary: bounty-board pays the
    //        escrow-market escrow cell THROUGH the shared `Payable` interface. ──
    let bounty = BountyTreasury::new(treasury_id, CREDIT);
    let payout_turn = bounty
        .payout(&operator, REWARD, escrow_id, InvokeAuthority::Signature)
        .expect("the bounty payout routes through Payable");

    // It is a payment through the shared interface: the desugared turn targets the
    // `pay` method and carries exactly ONE conserving kernel Transfer (treasury →
    // escrow). This is bounty-board paying escrow-market — not bespoke wiring.
    let payout_action = &payout_turn.call_forest.roots[0].action;
    assert_eq!(
        payout_action.method,
        method_symbol("pay"),
        "the payout is routed through the Payable `pay` method"
    );
    assert!(
        payout_action
            .effects
            .iter()
            .any(|e| matches!(e, Effect::Transfer { from, to, amount }
                if *from == treasury_id && *to == escrow_id && *amount == REWARD)),
        "the payout is a real Transfer crossing into the escrow cell"
    );

    exec.submit_turn(&payout_turn)
        .expect("the cross-app payout Transfer commits");

    assert_eq!(
        balance_of(&exec, treasury_id),
        0,
        "the bounty treasury paid out its reward"
    );
    assert_eq!(
        balance_of(&exec, escrow_id),
        REWARD as i64,
        "the escrow cell now HOLDS the credit a bounty paid it (value crossed the app boundary)"
    );
    assert_eq!(
        per_asset_supply(&exec, &CREDIT),
        0,
        "per-asset Σδ=0 still holds ACROSS the bounty→escrow boundary"
    );

    // ── (3) ESCROW SETTLES ONWARD: the escrow releases the held credit to the
    //        payee, again through the SAME shared `Payable` interface. ──
    let vault = EscrowVault::new(escrow_id, CREDIT);
    let settle_turn = vault
        .release(&operator, REWARD, payee_id, InvokeAuthority::Signature)
        .expect("the escrow settle-onward routes through Payable");
    let settle_action = &settle_turn.call_forest.roots[0].action;
    assert_eq!(
        settle_action.method,
        method_symbol("pay"),
        "the settle is routed through the same Payable `pay` method"
    );
    exec.submit_turn(&settle_turn)
        .expect("the escrow settle-onward Transfer commits");

    assert_eq!(
        balance_of(&exec, escrow_id),
        0,
        "the escrow released the credit onward"
    );
    assert_eq!(
        balance_of(&exec, payee_id),
        REWARD as i64,
        "the payee received the settled reward"
    );

    // ── (4) THE KEYSTONE ASSERTION: per-asset Σδ=0 across the WHOLE World after a
    //        value flow that touched TWO apps. mint → cross-boundary transfer →
    //        settle, and conservation held the entire way. ──
    assert_eq!(
        per_asset_supply(&exec, &CREDIT),
        0,
        "per-asset Σδ=0 across the WHOLE World after the cross-app flow"
    );
    // Explicitly: well(−REWARD) + treasury(0) + escrow(0) + payee(+REWARD) = 0.
    assert_eq!(balance_of(&exec, well_id), -(REWARD as i64));
    assert_eq!(balance_of(&exec, payee_id), REWARD as i64);
}

/// Both apps implement the SAME `Payable` DSI — the cross-app transfer is routed
/// through one shared, content-addressed interface, not per-pair wiring.
#[test]
fn both_apps_share_one_payable_interface() {
    let bounty = BountyTreasury::new(CellId::from_bytes([1u8; 32]), CREDIT);
    let vault = EscrowVault::new(CellId::from_bytes([2u8; 32]), CREDIT);
    use dregg_app_framework::Payable;
    let canonical = payable_descriptor().interface_id;
    assert_eq!(
        bounty.payable_interface().interface_id,
        canonical,
        "bounty-board speaks the canonical Payable interface"
    );
    assert_eq!(
        vault.payable_interface().interface_id,
        canonical,
        "escrow-market speaks the SAME canonical Payable interface"
    );
}
