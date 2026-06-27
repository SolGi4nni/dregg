//! The **Service Explorer** — a Postman-like surface for INVOKING cell methods,
//! interiorly, inside deos.
//!
//! Where [`crate::inspect_act`] fuses inspect→act over a cell's *affordance*
//! vocabulary (a fixed `{peek, touch, write, grant}` surface), the service
//! explorer is its **interface-typed** sibling: it discovers the methods a cell
//! actually publishes — its [`dregg_cell::InterfaceDescriptor`] — lets you pick
//! one, fill its arguments, and INVOKE it as a real verified turn.
//!
//! This is the deos-interior face of the `invoke()` front door
//! (`dregg_app_framework::invoke`): cells-as-service-objects method dispatch at
//! the USERSPACE layer. Crucially it adds NO kernel effect — there is no
//! `Effect::Invoke`. An invocation DESUGARS to an ordinary [`Action`] targeting
//! the method symbol and carrying the underlying existing effects the method
//! names; the kernel and the circuit keep seeing only effects they already know.
//! The one extra fact — that the invoked method is a member of the cell's
//! interface — is decided here by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses, not an
//! ad-hoc lookup.
//!
//! The interface itself is a USERSPACE object, NOT a committed cell field. The
//! explorer resolves it two ways, both commitment-free:
//!
//!   1. **derived from the cell's program** — [`InterfaceDescriptor::derive_replayable`]
//!      lifts every `MethodIs` guard in the cell's [`dregg_cell::CellProgram::Cases`]
//!      into a `Replayable` [`MethodSig`] (the methods the cell ACTUALLY dispatches
//!      on, with no extra declaration);
//!   2. **an explicit descriptor** an app registered (richer per-method
//!      auth/semantics than derive-from-program gives) — fed via
//!      [`ServiceExplorer::build_with_descriptor`].
//!
//! gpui-free and `cargo test`-able, exactly like [`crate::inspect_act`]: a test
//! discovers the methods off a real cell program, invokes a declared replayable
//! method (a real verified turn whose effect the re-inspection reflects), and
//! refuses an unknown method / an unauthorized one / a serviced one in-band.

use dregg_cell::interface::{InterfaceDescriptor, MethodSig, Semantics};
use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, CellId};
use dregg_turn::action::{
    symbol as method_symbol, Action, Authorization, CommitmentMode, DelegationMode, Effect,
};
use dregg_turn::turn::{Turn, TurnReceipt};

use crate::reflect::{self, Inspectable};
use crate::world::{CommitOutcome, World};

/// One **method the cell publishes**, as the explorer shows it for a viewer.
///
/// The interface-typed analogue of [`crate::inspect_act::Message`]: a routed
/// [`MethodSig`] presented inline, annotated with whether the viewer's held
/// authority satisfies the method's `auth_required` (the cap badge) and which
/// invocation class it falls in (replayable → invokable here; serviced → a
/// named seam that rides the OFE cross-cell-read, not a replay desugar).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MethodEntry {
    /// The method name (the human selector the user types/picks).
    pub name: String,
    /// The method symbol (the BLAKE3 hash an [`Action`] targets) the cell's
    /// `MethodIs` guard matches.
    pub symbol: [u8; 32],
    /// The argument arity the method declares (`Some(n)` for a fixed arity,
    /// `None` for variadic) — the explorer uses it to size the args input.
    pub arity: Option<u8>,
    /// What the caller must HOLD to invoke this method.
    pub required: AuthRequired,
    /// Replayable (desugars to its underlying effects, invokable here) vs
    /// Serviced (its answer rides the OFE cross-cell-read — the named seam).
    pub semantics: Semantics,
    /// **The cap badge.** `true` iff the viewer's authority satisfies `required`.
    pub authorized: bool,
}

impl MethodEntry {
    /// Is this method invokable through the explorer's replay-desugar path? A
    /// `Serviced` method is NOT (its answer is the named OFE seam, no effect
    /// desugar) — surfaced honestly, never hidden.
    pub fn is_invokable(&self) -> bool {
        self.semantics == Semantics::Replayable
    }
}

/// The result of INVOKING a method — the act half of the loop, with the
/// post-state re-inspected so the loop closes (invoke → inspect).
#[derive(Debug)]
pub enum InvokeOutcome {
    /// The invocation COMMITTED a real verified turn. Carries the executor's own
    /// [`TurnReceipt`] and the fresh [`Inspectable`] re-read off the POST-state
    /// ledger — the object you inspect next.
    Committed {
        receipt: Box<TurnReceipt>,
        reinspected: Inspectable,
    },
    /// The invocation was REFUSED, surfaced IN-BAND (never swallowed). `reason`
    /// names which gate fired; `by_executor` distinguishes the userspace
    /// front-door refusal (unknown/serviced/unauthorized method, before any
    /// turn) from the real executor rejecting the desugared turn (a guarantee
    /// fired: conservation, no-amplification, a permissions gate).
    Refused { reason: String, by_executor: bool },
}

impl InvokeOutcome {
    pub fn is_committed(&self) -> bool {
        matches!(self, InvokeOutcome::Committed { .. })
    }
}

/// **THE SERVICE EXPLORER VIEW** — a focused cell's discovered method interface
/// (cap-annotated for the viewer) plus its reflected state, built fresh off the
/// live [`World`].
///
/// The cockpit renders exactly this: the method list (each entry with its arity,
/// auth requirement, semantics, and cap badge) plus the reflected cell, and an
/// "invoke" affordance per authorized replayable method. [`ServiceExplorer::invoke`]
/// fires the chosen method through the real executor and hands back an
/// [`InvokeOutcome`] whose `reinspected` object the panel re-focuses on.
#[derive(Clone, Debug)]
pub struct ServiceExplorer {
    /// The cell whose service interface we are exploring.
    pub cell: CellId,
    /// The viewer principal the methods are projected FOR (whose held authority
    /// decides the cap badges).
    pub viewer: CellId,
    /// The viewer's authority over the cell (what gates the cap badges).
    pub viewer_rights: AuthRequired,
    /// The content-address of the resolved interface (the `interface_id`) — a
    /// stable handle a verifier could witness route-membership against.
    pub interface_id: [u8; 32],
    /// The reflected cell — the genuine [`reflect::reflect_cell`] view, read off
    /// the live ledger. `None` iff the focused cell is absent (a dangling focus).
    pub inspectable: Option<Inspectable>,
    /// The methods the cell publishes, AS THE VIEWER SEES THEM — every declared
    /// method, each annotated with arity, auth, semantics, and the cap badge.
    pub methods: Vec<MethodEntry>,
}

impl ServiceExplorer {
    /// Build the explorer for `cell` viewed by `viewer` holding `viewer_rights`,
    /// resolving the interface DERIVED from the cell's program.
    pub fn build(world: &World, cell: CellId, viewer: CellId, viewer_rights: AuthRequired) -> Self {
        let descriptor = world
            .ledger()
            .get(&cell)
            .map(|c| InterfaceDescriptor::derive_replayable(&c.program))
            .unwrap_or_else(|| InterfaceDescriptor::new(vec![]));
        Self::build_with_descriptor(world, cell, viewer, viewer_rights, &descriptor)
    }

    /// Build the explorer against an EXPLICIT interface descriptor (e.g. one an
    /// app registered with richer per-method auth/semantics than the derived
    /// interface gives).
    pub fn build_with_descriptor(
        world: &World,
        cell: CellId,
        viewer: CellId,
        viewer_rights: AuthRequired,
        descriptor: &InterfaceDescriptor,
    ) -> Self {
        // INSPECT — reuse reflect.rs; absent ⟹ honestly None (a dangling focus).
        let inspectable = world
            .ledger()
            .get(&cell)
            .map(|c| reflect::reflect_cell(&cell, c));

        // THE METHODS — every declared method, routed + annotated. We list ALL
        // declared methods (not only the authorized subset) so the explorer shows
        // the full interface AND which invocations are permitted (anti-ghost).
        let methods = descriptor
            .methods
            .iter()
            .map(|m| MethodEntry {
                name: method_name(descriptor, m),
                symbol: m.symbol,
                arity: arity_of(m),
                required: m.auth_required.clone(),
                semantics: m.semantics,
                authorized: authority_satisfies(&viewer_rights, &m.auth_required),
            })
            .collect();

        ServiceExplorer {
            cell,
            viewer,
            viewer_rights,
            interface_id: descriptor.interface_id,
            inspectable,
            methods,
        }
    }

    /// Look up a method entry by its short-hex label (the name the UI shows).
    pub fn method(&self, name: &str) -> Option<&MethodEntry> {
        self.methods.iter().find(|m| m.name == name)
    }

    /// Look up a method entry by its symbol (the stable identity the router
    /// classifies on — what the UI carries per row).
    pub fn method_by_symbol(&self, symbol: &[u8; 32]) -> Option<&MethodEntry> {
        self.methods.iter().find(|m| &m.symbol == symbol)
    }

    /// **Invoke a method by its cleartext NAME** — a convenience for callers that
    /// know the human method name (it hashes the name to its symbol and routes).
    /// The UI carries symbols (a derived interface has no cleartext), so it calls
    /// [`Self::invoke`] directly; this is for code that knows the name.
    pub fn invoke_named(
        &self,
        world: &mut World,
        name: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        viewer_rights: AuthRequired,
    ) -> InvokeOutcome {
        self.invoke(world, method_symbol(name), args, effects, viewer_rights)
    }

    /// **Invoke a method by its SYMBOL — the ACT half, closing the loop.**
    ///
    /// Resolves `symbol` against the cell's interface (re-deriving it off the live
    /// ledger so the routing is over the CURRENT program), routes it through the
    /// verified DFA router, gates its semantics (a `Serviced` method is the named
    /// seam — refused here, no replay desugar) and its `auth_required` against
    /// `viewer_rights`, then DESUGARS to an ordinary [`Action`] targeting
    /// `symbol` carrying `effects` (the underlying existing effects the method
    /// names — `SetField`, `Transfer`, … — supplied by the caller) and an `args`
    /// vector, wraps it in a [`Turn`], and commits through the real executor
    /// ([`World::commit_turn`]). On commit it re-inspects the cell off the
    /// post-state ledger (invoke → inspect).
    ///
    /// `effects` is the method's underlying body. A `Replayable` method IS a
    /// verified-turn template: the effects are its body, supplied by the caller,
    /// and the method symbol scopes the cell program's `MethodIs` case that
    /// constrains them. (`args` are the typed inputs the body reads.)
    pub fn invoke(
        &self,
        world: &mut World,
        symbol: [u8; 32],
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        viewer_rights: AuthRequired,
    ) -> InvokeOutcome {
        // The legible method handle (short-hex of the symbol) for refusal text.
        let method = reflect::short_hex(&symbol);
        // Re-resolve the interface off the LIVE program (the routing is over the
        // current cell, not a possibly-stale snapshot).
        let descriptor = match world.ledger().get(&self.cell) {
            Some(c) => InterfaceDescriptor::derive_replayable(&c.program),
            None => {
                return InvokeOutcome::Refused {
                    reason: format!(
                        "cell {} is absent from the ledger",
                        reflect::short_hex(self.cell.as_bytes())
                    ),
                    by_executor: false,
                };
            }
        };

        // (route) — the VERIFIED DFA router, not an ad-hoc find. Unknown ⟹ refused.
        let sig = match descriptor.route_method(&symbol) {
            Some(m) => m.clone(),
            None => {
                return InvokeOutcome::Refused {
                    reason: format!(
                        "the cell publishes no method with symbol `{}`",
                        reflect::short_hex(&symbol)
                    ),
                    by_executor: false,
                };
            }
        };

        // (semantics) — a Serviced method does not desugar to a replay effect.
        if sig.semantics == Semantics::Serviced {
            return InvokeOutcome::Refused {
                reason: format!(
                    "method `{method}` is a Serviced method — its answer rides the OFE \
                     cross-cell-read (a named seam), not a replay desugar"
                ),
                by_executor: false,
            };
        }

        // (cap-gate) — the method's declared authority vs the viewer's held rights.
        if !authority_satisfies(&viewer_rights, &sig.auth_required) {
            return InvokeOutcome::Refused {
                reason: format!(
                    "method `{method}` requires {:?}; the viewer's authority {:?} does not \
                     satisfy it (the cap-gate, before any turn)",
                    sig.auth_required, viewer_rights
                ),
                by_executor: false,
            };
        }

        // (desugar) — an ordinary Action targeting the method symbol carrying the
        // underlying existing effects. NO new Effect variant: the kernel/circuit
        // see only effects they already know.
        let action = Action {
            target: self.cell,
            method: symbol,
            args,
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let turn = self.wrap_invocation_turn(world, action);

        // (fire) — the embedded verified executor. Commit (a real receipt) or
        // reject (a guarantee fired) — both first-class, the rejection surfaced.
        match world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => {
                let reinspected = world
                    .ledger()
                    .get(&self.cell)
                    .map(|c| reflect::reflect_cell(&self.cell, c))
                    .unwrap_or_else(|| Inspectable {
                        kind: reflect::ObjectKind::Cell,
                        title: format!("Cell {} (gone)", reflect::short_hex(self.cell.as_bytes())),
                        subtitle: "the invocation retired this cell".to_string(),
                        fields: vec![],
                    });
                InvokeOutcome::Committed {
                    receipt,
                    reinspected,
                }
            }
            CommitOutcome::Rejected { reason, .. } => InvokeOutcome::Refused {
                reason,
                by_executor: true,
            },
            CommitOutcome::Queued { .. } => InvokeOutcome::Refused {
                reason: "the world is suspended; the invocation was staged in the pending queue \
                         and will run on resume"
                    .to_string(),
                by_executor: false,
            },
        }
    }

    /// Wrap a desugared invocation [`Action`] into a single-root [`Turn`] with
    /// the cell as the agent and its next nonce — via the real
    /// [`World::wrap_action_turn`] executor-entry (the operator is the authority;
    /// the cell `Permissions` + the executor's whole-turn guarantees still gate
    /// every effect). Preserves the action's `method` symbol verbatim.
    fn wrap_invocation_turn(&self, world: &World, action: Action) -> Turn {
        world.wrap_action_turn(self.cell, action)
    }

    /// Every line of text the explorer renders, flattened — so a test can assert
    /// the surface speaks real, cap-annotated text about the real interface.
    pub fn all_text(&self) -> Vec<String> {
        let mut out = Vec::new();
        out.push(format!(
            "service-explorer · cell {} · interface {} · viewer holds {:?}",
            reflect::short_hex(self.cell.as_bytes()),
            reflect::short_hex(&self.interface_id),
            self.viewer_rights
        ));
        out.push(format!("methods published: {}", self.methods.len()));
        for m in &self.methods {
            out.push(format!(
                "· {} (requires {:?}, {} args, {:?}) [{}]",
                m.name,
                m.required,
                m.arity
                    .map(|n| n.to_string())
                    .unwrap_or_else(|| "variadic".to_string()),
                m.semantics,
                if !m.is_invokable() {
                    "serviced — named seam"
                } else if m.authorized {
                    "you may invoke"
                } else {
                    "refused: insufficient authority"
                }
            ));
        }
        out
    }
}

// ── pure helpers (each names the real component) ──────────────────────────────

/// Does `held` authority satisfy a method's declared `required`? Mirrors the
/// `dregg_app_framework::invoke::InvokeAuthority::satisfies` tiers and the
/// executor's auth-tier semantics, expressed over the [`AuthRequired`] lattice
/// the cockpit threads (the viewer's held rights). `None` is always satisfiable;
/// `Impossible` never; the wider-or-equal relation is the proven attenuation
/// order (`required ⊆ held`).
fn authority_satisfies(held: &AuthRequired, required: &AuthRequired) -> bool {
    use dregg_cell::is_attenuation;
    match required {
        AuthRequired::None => true,
        AuthRequired::Impossible => false,
        // `required ⊆ held`: the held rights dominate (attenuate to) the required.
        _ => is_attenuation(held, required),
    }
}

/// The fixed arity a method declares (`Some(n)` for `Fixed(n)`, `None` for
/// `Variadic`) — the explorer uses it to size the args input.
fn arity_of(m: &MethodSig) -> Option<u8> {
    use dregg_cell::interface::ArgsSchema;
    match m.args_schema {
        ArgsSchema::Fixed(n) => Some(n),
        ArgsSchema::Variadic => None,
    }
}

/// The human name of a method. A [`MethodSig`] carries only its symbol (the
/// BLAKE3 hash), not the cleartext name, so the explorer shows the symbol's
/// short-hex as the legible handle (reversible to the routed method). When the
/// caller knows the cleartext name it can match by hashing — the symbol IS the
/// stable identity the router classifies on.
fn method_name(_descriptor: &InterfaceDescriptor, m: &MethodSig) -> String {
    reflect::short_hex(&m.symbol)
}

impl ServiceExplorer {
    /// [`ServiceExplorer::invoke`] against an EXPLICIT descriptor (e.g. an
    /// app-registered one with richer per-method auth/semantics than the
    /// derived-from-program interface). Routes/gates against `descriptor` rather
    /// than re-deriving from the program — so a `Signature`-gated or `Serviced`
    /// method declared only in the registry is honored.
    #[allow(clippy::too_many_arguments)]
    pub fn invoke_with_descriptor(
        &self,
        world: &mut World,
        descriptor: &InterfaceDescriptor,
        symbol: [u8; 32],
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        viewer_rights: AuthRequired,
    ) -> InvokeOutcome {
        let method = reflect::short_hex(&symbol);
        let sig = match descriptor.route_method(&symbol) {
            Some(m) => m.clone(),
            None => {
                return InvokeOutcome::Refused {
                    reason: format!("the interface publishes no method named `{method}`"),
                    by_executor: false,
                };
            }
        };
        if sig.semantics == Semantics::Serviced {
            return InvokeOutcome::Refused {
                reason: format!(
                    "method `{method}` is a Serviced method — its answer rides the OFE \
                     cross-cell-read (a named seam), not a replay desugar"
                ),
                by_executor: false,
            };
        }
        if !authority_satisfies(&viewer_rights, &sig.auth_required) {
            return InvokeOutcome::Refused {
                reason: format!(
                    "method `{method}` requires {:?}; the viewer's authority {:?} does not \
                     satisfy it (the cap-gate, before any turn)",
                    sig.auth_required, viewer_rights
                ),
                by_executor: false,
            };
        }
        let action = Action {
            target: self.cell,
            method: symbol,
            args,
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let turn = self.wrap_invocation_turn(world, action);
        match world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => {
                let reinspected = world
                    .ledger()
                    .get(&self.cell)
                    .map(|c| reflect::reflect_cell(&self.cell, c))
                    .unwrap_or_else(|| Inspectable {
                        kind: reflect::ObjectKind::Cell,
                        title: format!("Cell {} (gone)", reflect::short_hex(self.cell.as_bytes())),
                        subtitle: "the invocation retired this cell".to_string(),
                        fields: vec![],
                    });
                InvokeOutcome::Committed {
                    receipt,
                    reinspected,
                }
            }
            CommitOutcome::Rejected { reason, .. } => InvokeOutcome::Refused {
                reason,
                by_executor: true,
            },
            CommitOutcome::Queued { .. } => InvokeOutcome::Refused {
                reason: "the world is suspended; the invocation was staged".to_string(),
                by_executor: false,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig};
    use dregg_cell::program::{CellProgram, TransitionCase, TransitionGuard};

    /// Install a `Cases` program on a cell so its derived interface publishes the
    /// given methods, returning the cell id.
    fn cell_publishing(world: &mut World, seed: u8, method_names: &[&str]) -> CellId {
        let id = world.genesis_cell(seed, 1_000);
        let cases = method_names
            .iter()
            .map(|name| TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: method_symbol(name),
                },
                // No constraints: the case admits the transition (open program).
                constraints: vec![],
            })
            .collect();
        // Plus an Always-guarded catch-all so non-method writes still commit
        // (the executor default-denies a Cases program with no matching case).
        let mut all: Vec<TransitionCase> = cases;
        all.push(TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![],
        });
        assert!(world.set_cell_program(&id, CellProgram::Cases(all)));
        world.genesis_open_permissions(&id);
        id
    }

    #[test]
    fn explorer_discovers_methods_from_the_cell_program() {
        let mut w = World::new();
        let cell = cell_publishing(&mut w, 0x10, &["send", "dequeue"]);

        let se = ServiceExplorer::build(&w, cell, cell, AuthRequired::Either);

        // The reflected cell is the genuine reflect_cell view.
        let insp = se.inspectable.as_ref().expect("the cell exists");
        assert_eq!(insp.kind, reflect::ObjectKind::Cell);

        // The published methods are exactly the program's MethodIs guards (2),
        // each Replayable / None / variadic (the derive-from-program shape).
        assert_eq!(se.methods.len(), 2);
        for name in &["send", "dequeue"] {
            let entry = se
                .methods
                .iter()
                .find(|m| m.symbol == method_symbol(name))
                .unwrap_or_else(|| panic!("method {name} discovered"));
            assert_eq!(entry.semantics, Semantics::Replayable);
            assert_eq!(entry.required, AuthRequired::None);
            assert!(entry.is_invokable());
            assert!(entry.authorized, "None is satisfied by any viewer");
        }

        // The rendered text names the interface + the methods (a non-empty tree).
        assert!(se
            .all_text()
            .iter()
            .any(|l| l.contains("methods published: 2")));
    }

    #[test]
    fn invoking_a_replayable_method_commits_a_real_turn_the_reinspection_reflects() {
        let mut w = World::new();
        let cell = cell_publishing(&mut w, 0x20, &["write"]);

        let se = ServiceExplorer::build(&w, cell, cell, AuthRequired::Either);

        // Invoke `write` carrying its underlying existing effect (a real SetField
        // on slot 1). The desugared turn targets the method symbol.
        let effect = Effect::SetField {
            cell,
            index: 1,
            value: [9u8; 32],
        };
        let outcome = se.invoke(
            &mut w,
            method_symbol("write"),
            vec![[9u8; 32]],
            vec![effect],
            AuthRequired::Either,
        );
        let receipt = match outcome {
            InvokeOutcome::Committed { receipt, .. } => receipt,
            InvokeOutcome::Refused { reason, .. } => {
                panic!("an authorized replayable invoke should commit: {reason}")
            }
        };

        // It was a REAL verified turn whose action targeted the method symbol.
        assert_eq!(w.receipts().len(), 1, "the invoke committed a real turn");
        assert_eq!(receipt.agent, cell);

        // THE LOOP CLOSES: the live ledger reflects the SetField the invoke fired.
        assert_eq!(w.ledger().get(&cell).unwrap().state.fields[1], [9u8; 32]);

        // And the desugared action carried the method symbol (so the cell's
        // MethodIs case would scope it) — confirmed via the recorded turn.
        let last_turn = w
            .recorded_turns()
            .steps()
            .iter()
            .rev()
            .find_map(|s| match s {
                crate::replay::RecordedStep::Committed { turn, .. } => Some(turn.clone()),
                _ => None,
            })
            .expect("a committed turn was recorded");
        assert_eq!(
            last_turn.call_forest.roots[0].action.method,
            method_symbol("write"),
            "the desugared action targets the method symbol, not the zero method"
        );
    }

    #[test]
    fn invoking_an_unknown_method_is_refused_in_band() {
        let mut w = World::new();
        let cell = cell_publishing(&mut w, 0x30, &["send"]);
        let se = ServiceExplorer::build(&w, cell, cell, AuthRequired::Either);

        let outcome = se.invoke(
            &mut w,
            method_symbol("undeclared"),
            vec![],
            vec![Effect::IncrementNonce { cell }],
            AuthRequired::Either,
        );
        match outcome {
            InvokeOutcome::Refused {
                reason,
                by_executor,
            } => {
                assert!(
                    !by_executor,
                    "an unknown method is a userspace front-door refusal"
                );
                assert!(reason.contains("no method with symbol"));
            }
            InvokeOutcome::Committed { .. } => panic!("an unknown method cannot commit"),
        }
        assert_eq!(w.receipts().len(), 0, "no turn ran for an unknown method");
    }

    #[test]
    fn a_serviced_method_is_the_named_seam_refused_no_desugar() {
        // A registered descriptor marks `peek` Serviced — the explorer surfaces it
        // but refuses to desugar it (its answer rides the OFE cross-cell-read).
        let mut w = World::new();
        let cell = cell_publishing(&mut w, 0x40, &["peek"]);
        let descriptor = InterfaceDescriptor::new(vec![MethodSig {
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol("peek"))
        }]);

        let se = ServiceExplorer::build_with_descriptor(
            &w,
            cell,
            cell,
            AuthRequired::Either,
            &descriptor,
        );
        // The method is SHOWN (full vocabulary) but marked non-invokable.
        let entry = se
            .method(&reflect::short_hex(&method_symbol("peek")))
            .unwrap();
        assert_eq!(entry.semantics, Semantics::Serviced);
        assert!(!entry.is_invokable());

        // Invoke through the REGISTERED descriptor path so the Serviced semantics
        // is honored (the derive-from-program `invoke()` would see peek as a
        // Replayable program method). The serviced method is refused at the
        // userspace front door — its answer rides the OFE cross-cell-read, no
        // replay desugar — and runs no turn.
        let outcome = se.invoke_with_descriptor(
            &mut w,
            &descriptor,
            method_symbol("peek"),
            vec![],
            vec![],
            AuthRequired::Either,
        );
        assert!(
            matches!(&outcome, InvokeOutcome::Refused { reason, by_executor: false } if reason.contains("Serviced")),
            "a serviced method is the named seam, refused at the front door: {outcome:?}"
        );
        assert!(matches!(
            outcome,
            InvokeOutcome::Refused {
                by_executor: false,
                ..
            }
        ));
        assert_eq!(w.receipts().len(), 0);
    }

    #[test]
    fn an_unauthorized_invoke_is_refused_by_the_cap_gate() {
        // A registered descriptor requires Signature on `close`; a viewer holding
        // only Impossible (a foreign viewer) is refused at the cap-gate.
        let mut w = World::new();
        let cell = cell_publishing(&mut w, 0x50, &["close"]);
        let descriptor = InterfaceDescriptor::new(vec![MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol("close"))
        }]);

        // Build the view as a foreign viewer (Impossible authority).
        let se = ServiceExplorer::build_with_descriptor(
            &w,
            cell,
            cell,
            AuthRequired::Impossible,
            &descriptor,
        );
        let entry = se
            .method(&reflect::short_hex(&method_symbol("close")))
            .unwrap();
        assert!(!entry.authorized, "Signature ⊄ Impossible");

        // Invoke through the registered descriptor path: an explicit-descriptor
        // invoke routes against the descriptor (Signature-gated). A None/Impossible
        // viewer is refused before any turn.
        let outcome = se.invoke_with_descriptor(
            &mut w,
            &descriptor,
            method_symbol("close"),
            vec![],
            vec![Effect::IncrementNonce { cell }],
            AuthRequired::Impossible,
        );
        assert!(matches!(
            outcome,
            InvokeOutcome::Refused {
                by_executor: false,
                ..
            }
        ));
        assert_eq!(w.receipts().len(), 0);
    }

    #[test]
    fn authority_satisfies_the_attenuation_lattice() {
        assert!(authority_satisfies(
            &AuthRequired::None,
            &AuthRequired::None
        ));
        assert!(authority_satisfies(
            &AuthRequired::Either,
            &AuthRequired::Signature
        ));
        assert!(authority_satisfies(
            &AuthRequired::None,
            &AuthRequired::Either
        ));
        assert!(!authority_satisfies(
            &AuthRequired::Signature,
            &AuthRequired::Either
        ));
        assert!(!authority_satisfies(
            &AuthRequired::Impossible,
            &AuthRequired::Signature
        ));
        // Impossible required is never satisfied even by None.
        assert!(!authority_satisfies(
            &AuthRequired::None,
            &AuthRequired::Impossible
        ));
    }
}
