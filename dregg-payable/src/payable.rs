//! # `Payable` — the dregg standard interface for cross-app VALUE FLOW.
//!
//! `Payable` is a tiny, ocap-shaped, **conservation-respecting** standard for
//! "this cell can be paid / can pay", ERC-20-shaped but built on the kernel's
//! per-asset Σδ=0 value layer instead of a balance map an owner can mutate at
//! will:
//!
//! ```text
//!   pay(asset, amount, to)   — move `amount` of `asset` from THIS cell to `to`.
//!   balance(asset)           — read THIS cell's holding of `asset`.
//! ```
//!
//! ## It desugars to a REAL kernel `Effect::Transfer` — through the DFA router
//!
//! A `Payable` is NOT a new kernel effect and NOT a new commitment field. It is a
//! userspace [`InterfaceDescriptor`]. `pay` routes through the verified DFA router
//! ([`crate::routing::resolve_against`]) and desugars to the ONE effect the kernel
//! already conserves: an [`Effect::Transfer`] moving the asset between two cells
//! of one `World`/ledger. Because `Transfer` is `Conservative`
//! (`metatheory/Dregg2/Spec/Conservation.lean`; the Rust `LinearityClass` twin
//! was dead and is deleted) — per-asset Σδ=0 — a payment in one app becomes a
//! balance another app's cell
//! can spend — and the kernel conservation check holds ACROSS the app boundary.
//!
//! ## One source of truth, two callers
//!
//! [`resolve_pay`] is the verified desugar. The app framework's signed-turn `pay`
//! (the apps' `bounty.pay(reward, escrow)`) goes through it, AND the SDK's metered
//! tool-gateway charge goes through it — the SAME route table, the SAME `Signature`
//! cap gate, the SAME conserving `Transfer`, not a parallel hand-rolled effect.

use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_turn::Turn;
use dregg_turn::action::{Action, Effect};
use dregg_types::CellId;

use crate::routing::{InvokeAuthority, InvokeRefused, resolve_against};

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

/// Big-endian, right-aligned `u64 -> FieldElement` (the same convention as
/// `dregg_cell::program::field_from_u64_be`): the value occupies the trailing 8
/// bytes, the leading 24 bytes zero. Inlined here so the DSI core depends only on
/// `dregg-cell`/`dregg-turn`/`dregg-types`.
fn field_from_u64(value: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&value.to_be_bytes());
    out
}

/// The `pay` method signature: `(asset, amount, to)` — three field-element args,
/// `Signature`-gated (moving value requires the holder's authority), and
/// `Replayable` (it desugars to a pure verified [`Effect::Transfer`]).
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
/// `{pay, balance}` method set every `Payable` implementor shares. Its
/// `interface_id` is the same for every implementor (the DSI is a TYPE, not a
/// per-app object), so a holder can recognize "this cell speaks Payable" by its
/// id alone.
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
pub fn pay_args(asset: AssetId, amount: u64, to: CellId) -> Vec<FieldElement> {
    let mut to_felt = [0u8; 32];
    to_felt.copy_from_slice(to.as_bytes());
    vec![asset, field_from_u64(amount), to_felt]
}

/// **Resolve a `pay` through the `Payable` interface — THE verified desugar.**
///
/// Routes the `pay` method against the shared [`payable_descriptor`] (verified DFA
/// router → cap-gate on `Signature` → desugar), returning the UNSIGNED [`Action`]
/// carrying exactly the conserving [`Effect::Transfer`] and the matched
/// [`MethodSig`]. This is the one source of truth both the app framework's
/// signed-turn `pay` and the SDK tool-gateway charge go through — anyone holding
/// the resolved `(action, sig)` can confirm `action.method == pay` and the route
/// came from `payable_descriptor`.
///
/// `asset` should be `payer`'s `token_id` (a cell holds value only in its own
/// asset); it is bound into the invocation args as the payment's asset tag.
pub fn resolve_pay(
    payer: CellId,
    asset: AssetId,
    amount: u64,
    to: CellId,
    authority: InvokeAuthority,
) -> Result<(Action, MethodSig), InvokeRefused> {
    resolve_against(
        payer,
        &payable_descriptor(),
        PAY_METHOD,
        pay_args(asset, amount, to),
        pay_effects(payer, to, amount),
        authority,
    )
}

/// **A tiny turn-signer abstraction** so the [`Payable`] trait's signed-`Turn`
/// `pay` can live down here while the real signer (`AppCipherclerk`, which is
/// above the SDK) supplies the implementation up in `dregg-app-framework`.
///
/// `AppCipherclerk` already exposes `sign_action` / `make_turn` with exactly
/// these shapes, so it implements this trait with a one-line forwarding impl and
/// the apps' `cell.pay(cipherclerk, amount, to, authority)` call sites are
/// unchanged.
pub trait ActionSigner {
    /// Sign a resolved [`Action`] (binding the action hash under the signer's
    /// key + federation domain).
    fn sign_action(&self, action: Action) -> Action;
    /// Wrap a signed [`Action`] in a [`Turn`] with sane defaults, ready for the
    /// executor path.
    fn make_turn(&self, action: Action) -> Turn;
}

/// **The `Payable` DSI — implemented by an app so its value cell pays / is paid
/// through ONE shared interface.**
///
/// An app implements `Payable` on a small handle wrapping (a) the cell that holds
/// the value and (b) the asset it denominates value in. [`Payable::pay_resolved`]
/// is the verified, unsigned desugar (the SAME [`resolve_pay`] the SDK gateway
/// charge uses); [`Payable::pay`] signs it into a ready-to-submit [`Turn`] over an
/// [`ActionSigner`]. Any two `Payable` apps interoperate by default: a
/// bounty-board payout that pays an escrow-market escrow cell is
/// `bounty.pay(cipherclerk, reward, escrow, authority)`, the SAME call shape
/// escrow uses to settle onward — no per-pair wiring.
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

    /// **Resolve a payment to its verified, UNSIGNED desugar** — routes `pay`
    /// through the shared [`payable_descriptor`] to the conserving
    /// [`Effect::Transfer`], returning the `(Action, MethodSig)`. The cipherclerk-
    /// free core both [`Payable::pay`] and the SDK gateway charge ride.
    fn pay_resolved(
        &self,
        amount: u64,
        to: CellId,
        authority: InvokeAuthority,
    ) -> Result<(Action, MethodSig), InvokeRefused> {
        resolve_pay(
            self.payable_cell(),
            self.payable_asset(),
            amount,
            to,
            authority,
        )
    }

    /// Pay `amount` to `to`, through the shared `Payable` interface — the cross-app
    /// value-flow primitive. Desugars to a conserving kernel `Effect::Transfer`
    /// from [`Payable::payable_cell`], signed into a [`Turn`] via `signer`.
    fn pay<S: ActionSigner>(
        &self,
        signer: &S,
        amount: u64,
        to: CellId,
        authority: InvokeAuthority,
    ) -> Result<Turn, InvokeRefused> {
        let (action, _sig) = self.pay_resolved(amount, to, authority)?;
        let signed = signer.sign_action(action);
        Ok(signer.make_turn(signed))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn descriptor_is_canonical_and_routes_pay() {
        let d = payable_descriptor();
        assert!(d.verify_id(), "payable interface_id must be canonical");
        assert!(
            d.route_method(&method_symbol(PAY_METHOD)).is_some(),
            "pay must route"
        );
        assert!(
            d.route_method(&method_symbol(BALANCE_METHOD)).is_some(),
            "balance must route"
        );
        assert_eq!(d.interface_id, payable_descriptor().interface_id);
    }

    #[test]
    fn resolve_pay_desugars_to_a_single_conserving_transfer() {
        let from = cid(1);
        let to = cid(2);
        let (action, sig) = resolve_pay(from, [7u8; 32], 500, to, InvokeAuthority::Signature)
            .expect("pay must resolve through the Payable interface");

        // It targeted the pay method and desugared to exactly ONE kernel Transfer.
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
    fn resolve_pay_is_signature_gated() {
        let from = cid(1);
        let to = cid(2);
        let refused = resolve_pay(from, [7u8; 32], 500, to, InvokeAuthority::None)
            .expect_err("an unauthorized pay must be refused");
        assert!(matches!(refused, InvokeRefused::Unauthorized { .. }));
    }

    /// A minimal `Payable` impl proves the trait's verified core routes a payment
    /// to the conserving Transfer through the canonical descriptor.
    struct Wallet {
        cell: CellId,
        asset: AssetId,
    }
    impl Payable for Wallet {
        fn payable_cell(&self) -> CellId {
            self.cell
        }
        fn payable_asset(&self) -> AssetId {
            self.asset
        }
    }

    #[test]
    fn payable_impl_pay_resolved_routes_to_transfer() {
        let w = Wallet {
            cell: cid(1),
            asset: [3u8; 32],
        };
        let (action, _sig) = w
            .pay_resolved(250, cid(2), InvokeAuthority::Signature)
            .expect("pay_resolved routes through the canonical Payable interface");
        assert_eq!(action.method, method_symbol(PAY_METHOD));
        assert_eq!(action.effects.len(), 1);
        match action.effects[0] {
            Effect::Transfer { from, to, amount } => {
                assert_eq!(from, cid(1));
                assert_eq!(to, cid(2));
                assert_eq!(amount, 250);
            }
            ref other => panic!("the trait must route to a conserving Transfer, got {other:?}"),
        }
    }
}
