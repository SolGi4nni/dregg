//! # `Payable` — the dregg standard interface for cross-app VALUE FLOW.
//!
//! The interop census (`docs/deos/APPS-INTEROP-CENSUS.md`) found that across all
//! starbridge-apps NO value flows between apps: every app models money as scalar
//! `SetField`s on its own cell, never as a movable conserved asset crossing an
//! app boundary (0 `Effect::Transfer` / `Mint` / `Burn` in the whole gallery).
//! The keystone gap (#1) is a SHARED VALUE MEDIUM the apps actually transact
//! over; the #3 lesson (the ERC-20 lesson) is a SHARED, STANDARDIZED INTERFACE so
//! apps interoperate *by default* rather than via bespoke per-pair wiring.
//!
//! `Payable` is that interface: a tiny, ocap-shaped, **conservation-respecting**
//! standard for "this cell can be paid / can pay", ERC-20-shaped but built on the
//! kernel's per-asset Σδ=0 value layer instead of a balance map an owner can
//! mutate at will:
//!
//! ```text
//!   pay(asset, amount, to)   — move `amount` of `asset` from THIS cell to `to`.
//!   balance(asset)           — read THIS cell's holding of `asset`.
//! ```
//!
//! ## It desugars to a REAL kernel `Effect::Transfer` — through `invoke()`
//!
//! A `Payable` is NOT a new kernel effect and NOT a new commitment field. It is a
//! userspace [`InterfaceDescriptor`] (the same content-addressed, DFA-routed,
//! cap-gated interface object [`crate::invoke`] already speaks). `pay` routes
//! through the verified DFA router and desugars to the ONE effect the kernel
//! already conserves: an [`Effect::Transfer`] moving the asset between two cells
//! of one `World`/ledger. Because `Transfer` is `LinearityClass::Conservative`
//! (per-asset Σδ=0), a payment in one app becomes a balance another app's cell
//! can spend — and the kernel conservation check holds ACROSS the app boundary.
//!
//! The "asset" of a cell IS its `token_id` (`AssetId := issuer-cell`): a cell's
//! `state.balance()` is denominated in its `token_id`, and the per-asset standing
//! invariant is `Σ holders(asset) + well(asset) = 0`. So two apps interoperate in
//! one asset by holding cells of the SAME `token_id`; `pay` moves that conserved
//! quantity between them.
//!
//! ## Two apps implement it, so they pay each other through ONE interface
//!
//! `starbridge-bounty-board`'s reward treasury and `starbridge-escrow-market`'s
//! escrow holding cell each implement [`Payable`]. A bounty payout is
//! `bounty.pay(reward, escrow_cell)` — bounty-board paying escrow-market THROUGH
//! the shared interface, not bespoke wiring — and the escrow settles onward with
//! `escrow.pay(reward, payee)`. See
//! `starbridge-apps/escrow-market/tests/cross_app_value_flow.rs` for the proven
//! end-to-end flow (mint → cross-boundary transfer → settle → Σδ=0 across the
//! World).

use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_turn::Turn;
use dregg_turn::action::Effect;
use dregg_types::CellId;

use crate::cipherclerk::AppCipherclerk;
use crate::fields::field_from_u64;
use crate::invoke::{InvokeAuthority, InvokeRefused, invoke_with_descriptor};

/// A 32-byte asset identifier. In the dregg value model an asset IS its
/// issuer-cell (`AssetId := issuer-cell`): a holder cell's `state.balance()` is
/// denominated in the holder's `token_id`, and that `token_id` is the asset's
/// id. Two `Payable` cells interoperate in one asset by sharing a `token_id`.
pub type AssetId = [u8; 32];

/// The `pay(asset, amount, to)` method name — the verb that moves value out of a
/// `Payable` cell.
pub const PAY_METHOD: &str = "pay";
/// The `balance(asset)` method name — the read of a `Payable` cell's holding.
pub const BALANCE_METHOD: &str = "balance";

/// The `pay` method signature: `(asset, amount, to)` — three field-element args,
/// `Signature`-gated (moving value requires the holder's authority), and
/// `Replayable` (it desugars to a pure verified [`Effect::Transfer`] — a payment
/// re-executed against the same pre-state reproduces the same post-state, the
/// light-client replay model the kernel already enforces).
pub fn pay_method_sig() -> MethodSig {
    MethodSig {
        symbol: method_symbol(PAY_METHOD),
        args_schema: ArgsSchema::Fixed(3),
        auth_required: AuthRequired::Signature,
        semantics: Semantics::Replayable,
    }
}

/// The `balance` method signature: `(asset)` — one arg, openly readable
/// (`AuthRequired::None`), and `Serviced` (a balance answer rides the OFE
/// cross-cell read, not a pure-replay effect desugar; `invoke` does not fire it).
pub fn balance_method_sig() -> MethodSig {
    MethodSig {
        symbol: method_symbol(BALANCE_METHOD),
        args_schema: ArgsSchema::Fixed(1),
        auth_required: AuthRequired::None,
        semantics: Semantics::Serviced,
    }
}

/// The canonical `Payable` interface descriptor — the content-addressed
/// `{pay, balance}` method set every `Payable` app shares. Its `interface_id` is
/// the same for every implementor (the DSI is a TYPE, not a per-app object), so a
/// holder can recognize "this cell speaks Payable" by its id alone.
pub fn payable_descriptor() -> InterfaceDescriptor {
    InterfaceDescriptor::new(vec![pay_method_sig(), balance_method_sig()])
}

/// The underlying kernel effect a `pay` desugars to: a single conserving
/// [`Effect::Transfer`] of `amount` from the payer cell to `to`. This is the ONE
/// effect the kernel conserves per-asset (Σδ=0) — no `Mint`, no `Burn`, no scalar
/// `SetField` pretending to be money.
pub fn pay_effects(from: CellId, to: CellId, amount: u64) -> Vec<Effect> {
    vec![Effect::Transfer { from, to, amount }]
}

/// The `(asset, amount, to)` argument vector a `pay` invocation carries — a typed
/// witness of what was paid (the routing/auth happen on the method symbol; these
/// args are the receipt-bound record of the payment terms).
fn pay_args(asset: AssetId, amount: u64, to: CellId) -> Vec<FieldElement> {
    let mut to_felt = [0u8; 32];
    to_felt.copy_from_slice(to.as_bytes());
    vec![asset, field_from_u64(amount), to_felt]
}

/// **Pay `amount` of `asset` from `payer_cell` to `to`, THROUGH the `Payable`
/// interface.**
///
/// Routes the `pay` method against the shared [`payable_descriptor`] (verified
/// DFA router → cap-gate on `Signature` → desugar), then signs + wraps the
/// desugared [`Effect::Transfer`] in a [`Turn`] ready for the executor. The
/// returned turn carries ONLY the kernel `Transfer` the conservation check
/// already understands — there is no `Effect::Invoke`, no new commitment field.
///
/// `asset` should be `payer_cell`'s `token_id` (a cell holds value only in its
/// own asset); it is bound into the invocation args as the payment's asset tag.
/// The caller submits the returned turn through their executor (e.g.
/// [`crate::EmbeddedExecutor::submit_turn`]).
pub fn pay(
    cipherclerk: &AppCipherclerk,
    payer_cell: CellId,
    asset: AssetId,
    amount: u64,
    to: CellId,
    authority: InvokeAuthority,
) -> Result<Turn, InvokeRefused> {
    let descriptor = payable_descriptor();
    invoke_with_descriptor(
        cipherclerk,
        payer_cell,
        &descriptor,
        PAY_METHOD,
        pay_args(asset, amount, to),
        pay_effects(payer_cell, to, amount),
        authority,
    )
}

/// **The `Payable` DSI — implemented by an app so its value cell pays / is paid
/// through ONE shared interface.**
///
/// An app implements `Payable` on a small handle wrapping (a) the cell that holds
/// the value and (b) the asset it denominates value in. The default [`Payable::pay`]
/// routes a payment through the shared [`payable_descriptor`] to a real kernel
/// `Transfer`, so any two `Payable` apps interoperate by default: a bounty-board
/// payout that pays an escrow-market escrow cell is `bounty.pay(reward, escrow)`,
/// the SAME call shape escrow uses to settle onward — no per-pair wiring.
pub trait Payable {
    /// The cell that holds (and pays out) value — the `from` of a `pay`.
    fn payable_cell(&self) -> CellId;

    /// The asset this cell denominates value in (its `token_id`).
    fn payable_asset(&self) -> AssetId;

    /// The shared `Payable` interface this cell exposes. Every implementor
    /// returns the SAME content-addressed descriptor (the DSI is a type); an app
    /// only overrides this if it extends the interface.
    fn payable_interface(&self) -> InterfaceDescriptor {
        payable_descriptor()
    }

    /// Pay `amount` to `to`, through the shared `Payable` interface — the cross-app
    /// value-flow primitive. Desugars to a conserving kernel `Effect::Transfer`
    /// from [`Payable::payable_cell`]. `authority` is the holder authority the
    /// caller presents for the `Signature`-gated `pay`.
    fn pay(
        &self,
        cipherclerk: &AppCipherclerk,
        amount: u64,
        to: CellId,
        authority: InvokeAuthority,
    ) -> Result<Turn, InvokeRefused> {
        pay(
            cipherclerk,
            self.payable_cell(),
            self.payable_asset(),
            amount,
            to,
            authority,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::invoke::resolve_against;
    use dregg_cell::interface::Semantics;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn descriptor_is_canonical_and_routes_pay() {
        let d = payable_descriptor();
        // The DSI is a content-addressed TYPE: recompute matches the stored id.
        assert!(d.verify_id(), "payable interface_id must be canonical");
        // Both methods route through the verified DFA router.
        assert!(
            d.route_method(&method_symbol(PAY_METHOD)).is_some(),
            "pay must route"
        );
        assert!(
            d.route_method(&method_symbol(BALANCE_METHOD)).is_some(),
            "balance must route"
        );
        // The id is stable across constructions (every implementor shares it).
        assert_eq!(d.interface_id, payable_descriptor().interface_id);
    }

    #[test]
    fn pay_desugars_to_a_single_conserving_transfer() {
        let from = cid(1);
        let to = cid(2);
        let d = payable_descriptor();
        let (action, sig) = resolve_against(
            from,
            &d,
            PAY_METHOD,
            pay_args([7u8; 32], 500, to),
            pay_effects(from, to, 500),
            InvokeAuthority::Signature,
        )
        .expect("pay must resolve through the Payable interface");

        // It targeted the pay method and desugared to exactly ONE kernel Transfer
        // — the effect the per-asset Σδ=0 conservation check understands.
        assert_eq!(action.method, method_symbol(PAY_METHOD));
        assert_eq!(action.effects.len(), 1);
        match action.effects[0] {
            Effect::Transfer {
                from: f,
                to: t,
                amount,
            } => {
                assert_eq!(f, from);
                assert_eq!(t, to);
                assert_eq!(amount, 500);
            }
            ref other => panic!("pay must desugar to Transfer, got {other:?}"),
        }
        assert_eq!(sig.semantics, Semantics::Replayable);
    }

    #[test]
    fn pay_is_signature_gated() {
        // The pay method is Signature-gated: a caller presenting no authority is
        // refused at the front door (fail-closed), before any Transfer is built.
        let from = cid(1);
        let to = cid(2);
        let d = payable_descriptor();
        let refused = resolve_against(
            from,
            &d,
            PAY_METHOD,
            pay_args([7u8; 32], 500, to),
            pay_effects(from, to, 500),
            InvokeAuthority::None,
        )
        .expect_err("an unauthorized pay must be refused");
        assert!(matches!(refused, InvokeRefused::Unauthorized { .. }));
    }
}
