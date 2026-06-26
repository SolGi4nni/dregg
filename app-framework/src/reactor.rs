//! **`Reactor` — the reactive twin of [`invoke()`](crate::invoke) at the
//! USERSPACE layer.**
//!
//! [`invoke()`](crate::invoke) is the **command** front-door: a turn comes *in*
//! to a service-cell (caller-driven), the framework routes the method, cap-gates
//! it, and desugars to an ordinary [`Action`]. But a service that only answers
//! inbound commands is half a service. The other half is **reaction**: a service
//! that WATCHES a cell and, when an on-chain op it cares about commits, REACTS by
//! emitting its own turn — event-driven, not poke-driven. The on-chain
//! agent-loop.
//!
//! Before this module the only way to do that was to hand-wire, per service, the
//! node event-stream subscription + the match + the reaction-turn build. That
//! hand-wiring IS the gap: [`invoke()`](crate::invoke) prepared the command face;
//! nothing prepared the reaction face. `Reactor` is that face, made first-class.
//!
//! # The symmetry
//!
//! | | command ([`invoke`](crate::invoke)) | reaction ([`Reactor`]) |
//! |---|---|---|
//! | trigger | an inbound [`Action`] | an observed [`ObservedReceipt`] |
//! | declare | the cell's [`InterfaceDescriptor`](dregg_cell::InterfaceDescriptor) | a [`ReceiptFilter`] (what cells/ops it watches) |
//! | route | the verified DFA method router | [`ReceiptFilter::matches`] |
//! | decide | desugar method → underlying effects | [`Reactor::react`] → a [`ReactionPlan`] |
//! | cap-gate | [`InvokeAuthority::satisfies`] | the SAME [`InvokeAuthority::satisfies`] |
//! | fire | sign + wrap a [`Turn`] | sign + wrap a [`Turn`] |
//!
//! Both front-doors are **userspace**, exactly as the cells-as-service decision
//! requires: there is NO kernel `Effect::React` (just as there is no
//! `Effect::Invoke`). A reaction desugars to an ordinary [`Action`] carrying
//! ordinary effects the kernel already enforces and the circuit already
//! witnesses. The cell-commitment is untouched.
//!
//! # What `Reactor` wires (and what it does not)
//!
//! `Reactor` is the BUILD-the-reaction half — like [`invoke`](crate::invoke), it
//! does **no I/O**. The caller supplies the observed receipts (from the node's
//! event subscription — `NodeEvents`/`ReceiptFilter` over a live node, an
//! embedded executor's receipts in-process, or a test fixture) and submits the
//! returned [`Turn`]s through its executor. This keeps the abstraction pure,
//! testable without a node, and free of an async/transport dependency.
//!
//! A service implements [`Reactor`] by declaring two things:
//!
//! 1. [`Reactor::filter`] — **what it watches** (a [`ReceiptFilter`] over cells +
//!    methods; the reactive analogue of an interface descriptor).
//! 2. [`Reactor::react`] — **how it reacts** (an observed on-chain op → an
//!    optional [`ReactionPlan`]: the target/method/effects of the reaction turn,
//!    plus the authority the reaction requires).
//!
//! The framework wires the rest:
//!
//! - [`plan_reaction`] — match the filter, run [`Reactor::react`], cap-gate on the
//!   plan's [`AuthRequired`] (fail-closed), and desugar to an UNSIGNED [`Action`].
//! - [`react`] / [`react_build`] — sign with the reactor's cipherclerk and wrap a
//!   [`Turn`] ready for the executor.
//! - [`react_to_stream`] — drive a batch/stream of observed receipts, returning
//!   the reaction turns (the poll-loop's pure core).
//!
//! # Grounding
//!
//! This is the userspace reactive front-door over the proven reactive rung
//! (`docs/deos/REACTIVE-EFFECTS.md`): the soundness of a *standing, one-shot*
//! reaction (a promise-hole IS a nullifier) lives in `turn/src/reactive.rs`;
//! `Reactor` is the higher-layer convenience that lets a service DECLARE its
//! watch+react without re-plumbing the event-stream every time — the on-chain
//! agent-loop a service author actually writes.

use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_turn::Turn;
use dregg_turn::action::{Action, Effect, Symbol, symbol};
use dregg_types::CellId;

use crate::cipherclerk::AppCipherclerk;
use crate::invoke::InvokeAuthority;

/// **A committed receipt a [`Reactor`] OBSERVES** — the on-chain event the
/// node's subscription delivers. The reactive analogue of an inbound [`Action`].
///
/// Carries the committed turn's `target` cell (the cell that was written — e.g. a
/// command/mailbox cell), its `method` symbol, its committed `effects` (the
/// on-chain message body the reactor decodes), and the provenance handles
/// (`turn_hash` + `signer`) so a reaction can link back to what woke it.
#[derive(Clone, Debug)]
pub struct ObservedReceipt {
    /// The cell the observed turn targeted.
    pub cell: CellId,
    /// The method symbol of the observed turn.
    pub method: Symbol,
    /// The committed effects of the observed turn (the on-chain message body).
    pub effects: Vec<Effect>,
    /// The observed turn's hash — the receipt handle (provenance link).
    pub turn_hash: [u8; 32],
    /// The committing identity (the cell/public-key that signed the observed
    /// turn). A reactor that acts on a peer's behalf reads this to know *whose*
    /// op it is reacting to.
    pub signer: [u8; 32],
}

impl ObservedReceipt {
    /// Build an observation from a known [`Action`] (the in-process / embedded
    /// observer path: the executor that just committed the turn hands the reactor
    /// the action it ran, with the receipt's `turn_hash` + the `signer`). The
    /// live-node path constructs the same shape from the node's event stream.
    pub fn from_action(action: &Action, turn_hash: [u8; 32], signer: [u8; 32]) -> Self {
        Self {
            cell: action.target,
            method: action.method,
            effects: action.effects.clone(),
            turn_hash,
            signer,
        }
    }
}

/// Which cells a [`ReceiptFilter`] watches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WatchCells {
    /// Watch receipts on ANY cell (a broad observer; cap-gating / `react`'s own
    /// logic narrows what it acts on).
    Any,
    /// Watch only receipts targeting one of these cells (the common case — a
    /// service watching its command/mailbox cell).
    OneOf(Vec<CellId>),
}

impl WatchCells {
    fn contains(&self, cell: &CellId) -> bool {
        match self {
            WatchCells::Any => true,
            WatchCells::OneOf(cells) => cells.contains(cell),
        }
    }
}

/// Which methods/ops a [`ReceiptFilter`] watches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WatchMethods {
    /// React to any committed method on the watched cells.
    Any,
    /// React only to receipts whose method symbol is one of these.
    OneOf(Vec<Symbol>),
}

impl WatchMethods {
    /// Build a method watch from human-readable names (hashed to symbols).
    pub fn names(names: &[&str]) -> Self {
        WatchMethods::OneOf(names.iter().map(|n| symbol(n)).collect())
    }

    fn contains(&self, method: &Symbol) -> bool {
        match self {
            WatchMethods::Any => true,
            WatchMethods::OneOf(methods) => methods.contains(method),
        }
    }
}

/// **What a [`Reactor`] watches** — a predicate over observed receipts (cells +
/// ops). The reactive analogue of the [`InterfaceDescriptor`] that declares a
/// cell's command surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptFilter {
    /// The cells whose receipts this reactor observes.
    pub cells: WatchCells,
    /// The methods/ops this reactor reacts to.
    pub methods: WatchMethods,
}

impl ReceiptFilter {
    /// Watch one cell for a set of named methods (the common service case).
    pub fn cell_methods(cell: CellId, methods: &[&str]) -> Self {
        Self {
            cells: WatchCells::OneOf(vec![cell]),
            methods: WatchMethods::names(methods),
        }
    }

    /// Does `observed` fall within this filter? (cell ∧ method)
    pub fn matches(&self, observed: &ObservedReceipt) -> bool {
        self.cells.contains(&observed.cell) && self.methods.contains(&observed.method)
    }
}

/// **What a [`Reactor`] decides to DO on a match** — the reaction turn's
/// content, before signing. The reactive analogue of the desugared effects an
/// [`invoke`](crate::invoke)'d method names.
#[derive(Clone, Debug)]
pub struct ReactionPlan {
    /// The cell the reaction turn targets.
    pub target: CellId,
    /// The reaction method name (hashed to the action's method symbol).
    pub method: String,
    /// The reaction action's args.
    pub args: Vec<FieldElement>,
    /// The underlying existing effects the reaction commits (ordinary effects —
    /// the kernel/circuit see only what they already know).
    pub effects: Vec<Effect>,
    /// The authority this reaction requires — cap-gated against the reactor's
    /// presented [`InvokeAuthority`] before the turn is built (fail-closed).
    pub auth_required: AuthRequired,
}

/// **A service that watches a cell and reacts** — the reactive front-door a
/// service author implements. Declares its [`filter`](Reactor::filter) (what it
/// watches) and its [`react`](Reactor::react) (how it reacts); the framework
/// wires the match → cap-gate → build → sign.
pub trait Reactor {
    /// What this reactor watches.
    fn filter(&self) -> ReceiptFilter;

    /// How this reactor reacts to one observed receipt that passed its filter.
    /// `None` means "observed, but nothing to do" (e.g. an op this reactor
    /// recognizes but chooses to ignore). The framework calls this only for
    /// receipts that [`ReceiptFilter::matches`].
    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan>;
}

/// Why a reaction was refused at the userspace front door (before any turn is
/// built). Fail-closed: no effect is built, nothing is submitted. A non-match or
/// a `react`-returns-`None` is `Ok(None)`, not an error (silent, like an
/// [`invoke`](crate::invoke) of an unrouted method on a broad listener) — the
/// only refusal is the cap-gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReactRefused {
    /// The reaction's required authority is not satisfied by the reactor's
    /// presented [`InvokeAuthority`].
    Unauthorized {
        /// The reaction method.
        method: String,
        /// What the reaction requires.
        required: AuthRequired,
    },
}

impl std::fmt::Display for ReactRefused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unauthorized { method, required } => write!(
                f,
                "reaction `{method}` requires {required:?}; reactor authority is insufficient"
            ),
        }
    }
}

impl std::error::Error for ReactRefused {}

/// **Plan a reaction into an UNSIGNED [`Action`]** — the pure core (no
/// cipherclerk, no executor), mirroring [`crate::invoke::resolve_against`].
///
/// Returns `Ok(None)` when the receipt is not watched or the reactor chose not to
/// react; `Err(ReactRefused::Unauthorized)` when the reaction's `auth_required`
/// exceeds the presented authority; `Ok(Some(action))` with the desugared,
/// unsigned reaction action otherwise.
pub fn plan_reaction<R: Reactor + ?Sized>(
    reactor: &R,
    observed: &ObservedReceipt,
    authority: InvokeAuthority,
) -> Result<Option<Action>, ReactRefused> {
    // (1) Match the filter — what this reactor watches.
    if !reactor.filter().matches(observed) {
        return Ok(None);
    }
    // (2) Decide the reaction.
    let Some(plan) = reactor.react(observed) else {
        return Ok(None);
    };
    // (3) Cap-gate on the reaction's required authority (the SAME tiers
    //     invoke() gates a command on). Fail-closed before any turn is built.
    if !authority.satisfies(&plan.auth_required) {
        return Err(ReactRefused::Unauthorized {
            method: plan.method,
            required: plan.auth_required,
        });
    }
    // (4) Desugar to an ordinary Action — no new Effect variant; the reaction
    //     carries effects the kernel/circuit already know. Unsigned here; the
    //     cipherclerk path signs it.
    let action = Action {
        target: plan.target,
        method: symbol(&plan.method),
        args: plan.args,
        authorization: dregg_turn::action::Authorization::Unchecked,
        preconditions: Default::default(),
        effects: plan.effects,
        may_delegate: dregg_turn::action::DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: Vec::new(),
    };
    Ok(Some(action))
}

/// **Build the SIGNED reaction [`Turn`]** for one observed receipt — the
/// reactive analogue of [`invoke`](crate::invoke). Plans the reaction, then signs
/// with `cipherclerk` and wraps a [`Turn`] ready for the executor. Does no I/O:
/// the caller submits the returned turn.
pub fn react_build<R: Reactor + ?Sized>(
    cipherclerk: &AppCipherclerk,
    reactor: &R,
    observed: &ObservedReceipt,
    authority: InvokeAuthority,
) -> Result<Option<Turn>, ReactRefused> {
    match plan_reaction(reactor, observed, authority)? {
        Some(action) => {
            let signed = cipherclerk.sign_action(action);
            Ok(Some(cipherclerk.make_turn(signed)))
        }
        None => Ok(None),
    }
}

/// Alias for [`react_build`] — the named, one-receipt reaction front-door.
pub use react_build as react;

/// **Drive a batch/stream of observed receipts** — the pure core of a reactor's
/// poll loop. Returns one reaction [`Turn`] per receipt that matched + produced a
/// plan (in order). An [`ReactRefused`] aborts (the reactor's authority is
/// misconfigured — a setup error, not a per-receipt skip).
pub fn react_to_stream<R: Reactor + ?Sized>(
    cipherclerk: &AppCipherclerk,
    reactor: &R,
    observed: &[ObservedReceipt],
    authority: InvokeAuthority,
) -> Result<Vec<Turn>, ReactRefused> {
    let mut turns = Vec::new();
    for receipt in observed {
        if let Some(turn) = react_build(cipherclerk, reactor, receipt, authority)? {
            turns.push(turn);
        }
    }
    Ok(turns)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A toy reactor: watches `watched` for method `ping`, reacts by writing a
    /// `SetField` ack into `target`. The minimal exemplar that exercises the
    /// front-door (filter → react → cap-gate → build).
    struct PingReactor {
        watched: CellId,
        target: CellId,
        required: AuthRequired,
    }

    impl Reactor for PingReactor {
        fn filter(&self) -> ReceiptFilter {
            ReceiptFilter::cell_methods(self.watched, &["ping"])
        }

        fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
            // The reaction echoes the observed turn-hash into the target's slot 0.
            Some(ReactionPlan {
                target: self.target,
                method: "pong".to_string(),
                args: vec![],
                effects: vec![Effect::SetField {
                    cell: self.target,
                    index: 0,
                    value: observed.turn_hash,
                }],
                auth_required: self.required.clone(),
            })
        }
    }

    fn observed_ping(cell: CellId) -> ObservedReceipt {
        ObservedReceipt {
            cell,
            method: symbol("ping"),
            effects: vec![],
            turn_hash: [9u8; 32],
            signer: [1u8; 32],
        }
    }

    #[test]
    fn reacts_to_a_watched_op() {
        let watched = CellId([0xAu8; 32]);
        let target = CellId([0xBu8; 32]);
        let reactor = PingReactor {
            watched,
            target,
            required: AuthRequired::None,
        };
        let action = plan_reaction(&reactor, &observed_ping(watched), InvokeAuthority::None)
            .expect("no auth error")
            .expect("a watched ping must produce a reaction");
        assert_eq!(action.method, symbol("pong"));
        assert_eq!(action.target, target);
        match action.effects.as_slice() {
            [Effect::SetField { cell, index, value }] => {
                assert_eq!(*cell, target);
                assert_eq!(*index, 0);
                assert_eq!(
                    *value, [9u8; 32],
                    "the reaction binds the observed turn hash"
                );
            }
            other => panic!("expected one SetField, got {other:?}"),
        }
    }

    #[test]
    fn ignores_a_non_watched_cell() {
        let reactor = PingReactor {
            watched: CellId([0xAu8; 32]),
            target: CellId([0xBu8; 32]),
            required: AuthRequired::None,
        };
        // A ping on a DIFFERENT cell is not watched → Ok(None), no reaction.
        let other = observed_ping(CellId([0xCu8; 32]));
        assert!(matches!(
            plan_reaction(&reactor, &other, InvokeAuthority::None),
            Ok(None)
        ));
    }

    #[test]
    fn ignores_a_non_watched_method() {
        let watched = CellId([0xAu8; 32]);
        let reactor = PingReactor {
            watched,
            target: CellId([0xBu8; 32]),
            required: AuthRequired::None,
        };
        let mut obs = observed_ping(watched);
        obs.method = symbol("not-ping");
        assert!(matches!(
            plan_reaction(&reactor, &obs, InvokeAuthority::None),
            Ok(None)
        ));
    }

    #[test]
    fn cap_gates_the_reaction_fail_closed() {
        let watched = CellId([0xAu8; 32]);
        let reactor = PingReactor {
            watched,
            target: CellId([0xBu8; 32]),
            // The reaction requires a signature; a None-authority reactor must
            // be refused at the front door, before any turn is built.
            required: AuthRequired::Signature,
        };
        let refused = plan_reaction(&reactor, &observed_ping(watched), InvokeAuthority::None)
            .expect_err("a None reactor cannot satisfy a Signature reaction");
        assert!(matches!(refused, ReactRefused::Unauthorized { .. }));

        // ...but a Signature-holding reactor reacts.
        let ok = plan_reaction(
            &reactor,
            &observed_ping(watched),
            InvokeAuthority::Signature,
        )
        .expect("signature satisfies");
        assert!(ok.is_some());
    }

    #[test]
    fn drives_a_stream_of_observations() {
        let watched = CellId([0xAu8; 32]);
        let target = CellId([0xBu8; 32]);
        let reactor = PingReactor {
            watched,
            target,
            required: AuthRequired::None,
        };
        let cclerk = AppCipherclerk::new(crate::AgentCipherclerk::new(), [0u8; 32]);
        // Three observations: two watched pings + one off-cell that's skipped.
        let stream = vec![
            observed_ping(watched),
            observed_ping(CellId([0xCu8; 32])), // not watched → skipped
            observed_ping(watched),
        ];
        let turns = react_to_stream(&cclerk, &reactor, &stream, InvokeAuthority::None)
            .expect("no auth error");
        assert_eq!(turns.len(), 2, "two watched pings → two reaction turns");
    }
}
