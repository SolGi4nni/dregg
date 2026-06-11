//! # `raw` — UNAUTHORIZED turn construction. Genesis / plumbing ONLY.
//!
//! ## ⚠ READ THIS BEFORE IMPORTING ANYTHING FROM HERE
//!
//! This module is the SDK's **sealed escape hatch**: the raw
//! [`Action`]/[`Turn`] vocabulary, including [`Authorization::Unchecked`] —
//! the one value that expresses *an act carrying no credential at all*.
//!
//! It exists for exactly three legitimate reasons:
//!
//! 1. **Genesis construction** — seeding a brand-new world before any key
//!    or capability exists to authorize with (node init, test-world
//!    fixtures, faucet genesis moves).
//! 2. **The signing flow itself** — the canonical signing message is
//!    computed over the action *with the authorization field zeroed*
//!    ([`unsigned_action`] is that zeroing step, used internally by
//!    [`AgentCipherclerk::sign_action`](crate::AgentCipherclerk::sign_action)
//!    and the [`AgentRuntime`](crate::AgentRuntime) execute paths before the
//!    real signature is attached).
//! 3. **Sovereign / proof-carrying turns** — a sovereign cell's authority is
//!    its witness or STARK proof, not an Ed25519 signature; those turns
//!    structurally carry no signature leg.
//!
//! **Everything else goes through the authorized surface**: an identity
//! ([`AgentCipherclerk`](crate::AgentCipherclerk)) building a turn via
//! [`AgentRuntime::turn()`](crate::AgentRuntime::turn) → typed verb builders
//! → [`sign()`](crate::turns::TurnBuilder::sign) →
//! [`submit()`](crate::turns::AuthorizedTurn::submit), or the
//! [`factories`](crate::factories) / [`polis`](crate::polis) plan builders.
//! On that surface an unauthorized act is **inexpressible** — the
//! authorization field is private to the flow and always a real credential
//! by the time anything executes.
//!
//! If you find yourself importing from `raw` in application code, you are
//! almost certainly building something the executor will reject (or worse,
//! something a permissive test ledger will silently accept and the real
//! network will not). The executor's posture is documented in
//! `turn/src/action.rs`: `Unchecked` means "no credential presented;
//! ownership / cell-permission checks decide", and any cell with real
//! permissions rejects it.

use dregg_cell::CellId;

// The raw turn-construction vocabulary, quarantined here so the crate root
// can present only the authorized surface. These are exactly the
// `dregg_turn` types; nothing is wrapped or weakened — the seal is the
// module boundary and its documentation, not a type change (the wire
// format is untouched).
pub use dregg_turn::{
    Action, Authorization, CallForest, CommitmentMode, DelegationMode, Effect, TokenKeyRef, Turn,
    TurnReceipt, WitnessedReceipt,
};

/// The raw per-action builder from `dregg-turn` (its only unauthorized
/// constructor is loudly named `new_unchecked_for_tests`).
pub use dregg_turn::builder::ActionBuilder;

/// The raw turn-skeleton builder from `dregg-turn`.
pub use dregg_turn::TurnBuilder as RawTurnBuilder;

/// `symbol(name)` — the method-name hash actions carry.
pub use dregg_turn::action::symbol;

/// Build the UNAUTHORIZED action scaffold: `authorization =
/// Authorization::Unchecked`, every optional field defaulted.
///
/// This is the **one** place the SDK spells `Authorization::Unchecked` for
/// construction. Its two sanctioned uses:
///
/// * as the zero-authorization input to the canonical signing message
///   (the signing flow immediately replaces the field with a real
///   `Authorization::Signature`);
/// * as the body of genesis / sovereign / proof-carrying turns whose
///   authority is decided by something other than a signature leg
///   (ownership at genesis, the sovereign witness, the attached STARK).
///
/// An action built here and submitted as-is presents **no credential**:
/// the executor admits it only where the target cell's own permissions
/// say nothing is required.
pub fn unsigned_action(target: CellId, method: [u8; 32], effects: Vec<Effect>) -> Action {
    Action {
        target,
        method,
        args: Vec::new(),
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

/// [`unsigned_action`] with a string method name (hashed via [`symbol`]).
pub fn unsigned_action_named(target: CellId, method: &str, effects: Vec<Effect>) -> Action {
    unsigned_action(target, symbol(method), effects)
}
