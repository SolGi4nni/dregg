//! THE SETTLEMENT FAMILIES & FACTORY-AUTHORING CAPSTONE (L10) — verified app
//! authoring on the moldable-inspector spine.
//!
//! L1 (`presentable.rs`) is the framework; L2 (`predicate_composer.rs`) is the
//! caveat language; L3 (`turn_builder.rs`) is the universal construction gadget.
//! L10 is the capstone that FUSES them into "author a real, verified userspace
//! app end-to-end" (`docs/deos/INSPECTOR-FRAMEWORK.md` Part 3 §L10, census
//! slices 10-settlement + 12-factory — the settlement-family true-zeros).
//!
//! An app, on dregg, is a per-deal [`FactoryDescriptor`]: a content-addressed
//! birth-template whose `state_constraints` are exactly the perpetual slot
//! caveats every child it births carries on its `CellProgram` (the executor
//! gates EVERY subsequent turn against them). The settlement families
//! (`cell/src/blueprint.rs`) are the proven instances — escrow, obligation,
//! bridge, channel — each a `*_factory_descriptor(terms)` whose constraint set
//! realizes the Lean settlement keystones (conservation · no-double-resolve ·
//! condition-gated release · monotone redemption).
//!
//! This module gives that family:
//!
//!   * **The Presentable face.** [`ReflectedFactory`] presents a deployed
//!     descriptor: the [`PresentationKind::RawFields`] floor is `reflect.rs`'s
//!     `reflect_factory` verbatim, plus a `Source` "what the factory produces"
//!     prose and an `Invariant` readout of the perpetual caveats every child
//!     inherits. [`ReflectedSettlement`] presents the deal terms of a settlement
//!     family — its `DomainVisual` is the deal's real lifecycle STATE MACHINE
//!     (open → released/refunded; locked → finalized/cancelled; …) and its
//!     `Invariant` is the conservation/settlement guarantee the constraint set
//!     enforces, read off the GENUINE `*_state_constraints(terms)`.
//!
//!   * **The factory-authoring gadget.** [`FactoryAuthor`] is the
//!     [`CommittingGadget`] that fuses L2 + L3: it COMPOSES a child cell-program
//!     out of `predicate_composer`'s real atoms (reusing [`Composite`]/the
//!     genuine `StateConstraint` lowering — never a parallel predicate model),
//!     wraps it as a [`FactoryDescriptor`] blueprint, DEPLOYS it via the real
//!     [`World::deploy_factory`] (the executor's content-addressed registry),
//!     and BIRTHS a child via `create_cell_from_factory` — riding
//!     `turn_builder`/`simulate.rs`'s predict-then-commit spine so the birth is
//!     the IDENTICAL verified turn the executor runs. A child born under
//!     conservation through the real executor; an unregistered / over-reaching
//!     factory REFUSED by that same executor.
//!
//! gpui-free + `cargo test`-able exactly as the sibling lanes are: the model is
//! pure data, every method takes `&World`/`&mut World` and returns data, and the
//! tests assert the model (a composed factory deploys + a child is born under
//! conservation, an unregistered factory rejects, the settlement presentations
//! reflect real blueprint state).

use dregg_cell::blueprint::{
    self, BridgeTerms, ChannelTerms, EscrowTerms, ObligationTerms, TrustlineTerms,
};
use dregg_cell::factory::{
    CapTarget, CapTemplate, ChildVkStrategy, FactoryCreationParams, FactoryDescriptor,
    canonical_program_vk,
};
use dregg_cell::program::StateConstraint;
use dregg_cell::{AuthRequired, CellId, CellMode, CellProgram};

use crate::predicate_composer::{Composite, PredicateComposer};
use crate::presentable::{
    Gadget, GadgetError, GadgetField, GadgetInput, GadgetValidation, PresentCtx, Presentable,
    Presentation, PresentationBody, PresentationKind, SmState, SmTransition, StateMachineView,
};
use crate::reflect::{self, Field, Inspectable, ObjectKind};
use crate::world::{CommitOutcome, World, create_cell_from_factory};

// ===========================================================================
// §L10.1 — ReflectedFactory: the deployed-descriptor Presentable face.
// ===========================================================================

/// A thin newtype wrapping a deployed [`FactoryDescriptor`] as a [`Presentable`]
/// — the birth-template's legible faces. The descriptor lives in the foreign
/// `dregg_cell` crate, so we present via this wrapper (the established
/// reflect-a-foreign-struct pattern, like `ReflectedCell`). The presentations
/// read the genuine descriptor: `reflect_factory` for the floor, the real
/// `state_constraints` for the inherited-invariant readout.
#[derive(Clone, Debug)]
pub struct ReflectedFactory {
    /// The genuine deployed descriptor being presented.
    pub descriptor: FactoryDescriptor,
    /// The content-addressed VK the executor's registry keys it on (`deploy`'s
    /// return). `None` if presenting a not-yet-deployed blueprint.
    pub deployed_vk: Option<[u8; 32]>,
}

impl ReflectedFactory {
    /// Wrap a descriptor for presentation (not necessarily deployed yet).
    pub fn new(descriptor: FactoryDescriptor) -> Self {
        ReflectedFactory {
            descriptor,
            deployed_vk: None,
        }
    }

    /// Wrap a deployed descriptor, carrying the VK its registry entry is keyed on.
    pub fn deployed(descriptor: FactoryDescriptor, vk: [u8; 32]) -> Self {
        ReflectedFactory {
            descriptor,
            deployed_vk: Some(vk),
        }
    }

    /// The "what this factory produces" Source prose, read off the genuine
    /// descriptor (its child program pin, cap templates, perpetual caveats).
    pub fn source_prose(&self) -> String {
        let d = &self.descriptor;
        let mut s = format!(
            "A {:?} factory (content-addressed VK {}). Every child it births:\n",
            d.default_mode,
            reflect::short_hex(&d.factory_vk)
        );
        match d.child_program_vk {
            Some(vk) => s.push_str(&format!(
                "  · carries the pinned child program (VK {})\n",
                reflect::short_hex(&vk)
            )),
            None => s.push_str("  · carries no pinned child program (sovereign-witnessed)\n"),
        }
        s.push_str(&format!(
            "  · inherits {} perpetual slot caveat(s) (the executor gates every \
             subsequent turn against them)\n",
            d.state_constraints.len()
        ));
        s.push_str(&format!(
            "  · may be granted up to {} cap template(s)\n",
            d.allowed_cap_templates.len()
        ));
        if let Some(budget) = d.creation_budget {
            s.push_str(&format!(
                "  · is rate-limited to {budget} birth(s) per epoch\n"
            ));
        }
        s
    }
}

impl Presentable for ReflectedFactory {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Factory
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the genuine reflect_factory.
        let insp = reflect::reflect_factory(&self.descriptor);
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Factory".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Source — "what the factory produces" (the constructor contract).
        let prose = self.source_prose();
        out.push(Presentation {
            kind: PresentationKind::Source,
            label: "What it produces".to_string(),
            search_text: format!("source {prose}"),
            body: PresentationBody::Prose(prose),
        });

        // (3) Invariant — the perpetual caveats every child inherits, read off
        //     the GENUINE state_constraints (the same predicate the executor
        //     installs on the born cell + gates every turn against).
        let inv = inherited_invariant_prose(&self.descriptor.state_constraints);
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Inherited invariants".to_string(),
            search_text: format!("invariant {inv}"),
            body: PresentationBody::Prose(inv),
        });

        out
    }
}

/// The prose of the perpetual caveats a factory's children inherit — read off
/// the genuine [`StateConstraint`] set (never a parallel paraphrase).
fn inherited_invariant_prose(constraints: &[StateConstraint]) -> String {
    if constraints.is_empty() {
        return "no perpetual slot caveats — children are unconstrained after birth.".to_string();
    }
    let mut s = format!(
        "Every born child carries {} perpetual slot caveat(s), enforced by the \
         executor on EVERY turn that touches the cell:\n",
        constraints.len()
    );
    for (i, c) in constraints.iter().enumerate() {
        s.push_str(&format!(
            "  [{i}] {}\n",
            format!("{c:?}").chars().take(96).collect::<String>()
        ));
    }
    s
}

// ===========================================================================
// §L10.2 — ReflectedSettlement: the settlement-family deal-terms face.
// ===========================================================================

/// One of the proven settlement families — the deal-terms object an author
/// publishes (`cell/src/blueprint.rs`). Each carries the family's `terms` and
/// lowers to the genuine `*_factory_descriptor(terms)` + the deal's real
/// lifecycle state machine.
#[derive(Clone, Debug)]
pub enum SettlementFamily {
    /// An escrow deal (open → released | refunded).
    Escrow(EscrowTerms),
    /// A bonded proof obligation (open → fulfilled | slashed).
    Obligation(ObligationTerms),
    /// A cross-domain bridge lock (locked → finalized | cancelled).
    Bridge(BridgeTerms),
    /// A directional trustline (uninit → open → closed).
    Trustline(TrustlineTerms),
    /// A channel group (uninit → open → closed).
    Channel(ChannelTerms),
}

impl SettlementFamily {
    /// The family's name (the DomainVisual tab + Source heading).
    pub fn name(&self) -> &'static str {
        match self {
            SettlementFamily::Escrow(_) => "Escrow",
            SettlementFamily::Obligation(_) => "Obligation",
            SettlementFamily::Bridge(_) => "Bridge",
            SettlementFamily::Trustline(_) => "Trustline",
            SettlementFamily::Channel(_) => "Channel",
        }
    }

    /// Lower the family to its genuine [`FactoryDescriptor`] — the real
    /// per-deal content-addressed blueprint (`cell/src/blueprint.rs`). Fails
    /// closed on a malformed deal (zero condition / zero line / …), surfacing
    /// the blueprint's own refusal.
    pub fn descriptor(&self) -> Result<FactoryDescriptor, GadgetError> {
        let r = match self {
            SettlementFamily::Escrow(t) => blueprint::escrow_factory_descriptor(t),
            SettlementFamily::Obligation(t) => blueprint::obligation_factory_descriptor(t),
            SettlementFamily::Bridge(t) => blueprint::bridge_factory_descriptor(t),
            SettlementFamily::Trustline(t) => blueprint::trustline_factory_descriptor(t),
            SettlementFamily::Channel(t) => blueprint::channel_factory_descriptor(t),
        };
        r.map_err(|e| GadgetError::Lowering {
            reason: format!("{} blueprint refused the deal terms: {e:?}", self.name()),
        })
    }

    /// The deal's real lifecycle [`StateMachineView`] — the states + the verb
    /// transitions of THIS settlement family. The shapes mirror the blueprints'
    /// `AllowedTransitions` / dual-resolution teeth.
    pub fn state_machine(&self) -> StateMachineView {
        match self {
            SettlementFamily::Escrow(_) => dual_resolution_sm(
                "Open",
                ("Released", "Release (condition met → beneficiary)"),
                ("Refunded", "Refund (timeout → depositor)"),
            ),
            SettlementFamily::Obligation(_) => dual_resolution_sm(
                "Posted",
                ("Fulfilled", "Fulfil (condition met → obligor)"),
                ("Slashed", "Slash (deadline passed → obligee)"),
            ),
            SettlementFamily::Bridge(_) => dual_resolution_sm(
                "Locked",
                ("Finalized", "Finalize (finality witness → pot)"),
                ("Cancelled", "Cancel (timeout → originator)"),
            ),
            SettlementFamily::Trustline(_) => lifecycle_sm("Open", "Closed", "Close"),
            SettlementFamily::Channel(_) => lifecycle_sm("Open", "Closed", "Close"),
        }
    }
}

/// A two-outcome settlement state machine (the escrow/obligation/bridge shape):
/// one live state that resolves to one of two TERMINAL outcomes (the
/// no-double-resolve tooth — both outcomes are terminal).
fn dual_resolution_sm(live: &str, a: (&str, &str), b: (&str, &str)) -> StateMachineView {
    StateMachineView {
        states: vec![
            SmState {
                name: live.to_string(),
                terminal: false,
            },
            SmState {
                name: a.0.to_string(),
                terminal: true,
            },
            SmState {
                name: b.0.to_string(),
                terminal: true,
            },
        ],
        transitions: vec![
            SmTransition {
                from: live.to_string(),
                to: a.0.to_string(),
                verb: a.1.to_string(),
            },
            SmTransition {
                from: live.to_string(),
                to: b.0.to_string(),
                verb: b.1.to_string(),
            },
        ],
        current: live.to_string(),
    }
}

/// A linear lifecycle (uninit → live → terminal-closed) — the trustline/channel
/// shape (CLOSED is inert; no row out).
fn lifecycle_sm(live: &str, closed: &str, close_verb: &str) -> StateMachineView {
    StateMachineView {
        states: vec![
            SmState {
                name: "Uninit".to_string(),
                terminal: false,
            },
            SmState {
                name: live.to_string(),
                terminal: false,
            },
            SmState {
                name: closed.to_string(),
                terminal: true,
            },
        ],
        transitions: vec![
            SmTransition {
                from: "Uninit".to_string(),
                to: live.to_string(),
                verb: "Open".to_string(),
            },
            SmTransition {
                from: live.to_string(),
                to: closed.to_string(),
                verb: close_verb.to_string(),
            },
        ],
        current: "Uninit".to_string(),
    }
}

impl Presentable for SettlementFamily {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Factory
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the deal terms as a field tree.
        let insp = settlement_inspectable(self);
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: format!("{} terms", self.name()),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) DomainVisual — the deal's real lifecycle STATE MACHINE.
        let sm = self.state_machine();
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: format!("{} lifecycle", self.name()),
            search_text: format!(
                "lifecycle {} {}",
                sm.current,
                sm.states
                    .iter()
                    .map(|s| s.name.as_str())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            body: PresentationBody::StateMachine(sm),
        });

        // (3) Invariant — the conservation / settlement guarantee, read off the
        //     GENUINE descriptor's state_constraints (the proven keystones).
        let prose = match self.descriptor() {
            Ok(d) => {
                let mut s = format!(
                    "{} conserves value (the locked amount lives in the deal cell's own \
                     balance; funding + settling are ordinary Σδ=0 Transfers) and resolves \
                     at most once (both outcomes are terminal — the no-double-resolve tooth).\n\n",
                    self.name()
                );
                s.push_str(&inherited_invariant_prose(&d.state_constraints));
                s
            }
            Err(e) => format!("the deal terms are malformed: {e:?}"),
        };
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Settlement guarantee".to_string(),
            search_text: format!("invariant {prose}"),
            body: PresentationBody::Prose(prose),
        });

        out
    }
}

/// Project a settlement family's deal terms into a [`Inspectable`] floor.
fn settlement_inspectable(fam: &SettlementFamily) -> Inspectable {
    let (subtitle, fields): (String, Vec<Field>) = match fam {
        SettlementFamily::Escrow(t) => (
            "open → released | refunded".to_string(),
            vec![
                Field::count("amount", t.amount),
                Field::count("timeout_height", t.timeout_height),
                Field::hash("depositor", t.depositor),
                Field::hash("beneficiary", t.beneficiary),
                Field::hash("condition", t.condition),
            ],
        ),
        SettlementFamily::Obligation(t) => (
            "posted → fulfilled | slashed".to_string(),
            vec![
                Field::count("bond", t.bond),
                Field::count("deadline_height", t.deadline_height),
                Field::hash("obligor", t.obligor),
                Field::hash("obligee", t.obligee),
                Field::hash("condition", t.condition),
            ],
        ),
        SettlementFamily::Bridge(t) => (
            "locked → finalized | cancelled".to_string(),
            vec![
                Field::count("amount", t.amount),
                Field::count("timeout_height", t.timeout_height),
                Field::hash("originator", t.originator),
                Field::hash("pot", t.pot),
                Field::hash("finality_witness", t.finality_witness),
            ],
        ),
        SettlementFamily::Trustline(t) => (
            "uninit → open → closed".to_string(),
            vec![
                Field::count("line", t.line),
                Field::hash("issuer", t.issuer),
                Field::hash("holder", t.holder),
            ],
        ),
        SettlementFamily::Channel(t) => (
            "uninit → open → closed".to_string(),
            vec![Field::hash("admin", t.admin), Field::hash("tag", t.tag)],
        ),
    };
    Inspectable {
        kind: ObjectKind::Factory,
        title: format!("{} deal terms", fam.name()),
        subtitle,
        fields,
    }
}

// ===========================================================================
// §L10.3 — FactoryAuthor: the factory-authoring CommittingGadget (L2 ⊗ L3).
// ===========================================================================

/// What a [`FactoryAuthor`] builds — a deployable [`FactoryDescriptor`] wrapping
/// the composed child cell-program.
pub type AuthoredFactory = FactoryDescriptor;

/// The outcome of authoring a factory end-to-end: deploy → birth a child.
#[derive(Clone, Debug)]
pub enum AuthoringOutcome {
    /// The factory deployed AND a child was born under conservation through the
    /// real executor; carries the deployed VK, the birth receipt, and the child id.
    Born {
        /// The factory's content-addressed VK (its registry key).
        factory_vk: [u8; 32],
        /// The receipt hash of the verified birth turn.
        receipt_hash: [u8; 32],
        /// The born child's [`CellId`] (`derive_raw(owner, token)`).
        child: CellId,
    },
    /// The birth turn was REFUSED by the executor (an unregistered /
    /// over-reaching factory, a non-conserving birth) — the reason it pinned.
    Refused { reason: String },
}

impl AuthoringOutcome {
    /// `true` iff a child was born (the factory deployed + the birth committed).
    pub fn born(&self) -> bool {
        matches!(self, AuthoringOutcome::Born { .. })
    }

    /// The born child's id, if a child was born.
    pub fn child(&self) -> Option<CellId> {
        match self {
            AuthoringOutcome::Born { child, .. } => Some(*child),
            AuthoringOutcome::Refused { .. } => None,
        }
    }
}

/// THE FACTORY-AUTHORING GADGET — the L10 capstone that FUSES L2 + L3.
///
/// It COMPOSES a child cell-program out of `predicate_composer`'s genuine atoms
/// (the [`Composite`] the author builds, lowered to a real `StateConstraint`),
/// wraps it as a per-app [`FactoryDescriptor`] blueprint (content-addressed the
/// way `cell/src/blueprint.rs`'s settlement descriptors are — `child_program_vk`
/// = `canonical_program_vk(program)`, a `Fixed` VK strategy, a self-cell
/// signature cap template), DEPLOYS it via the real [`World::deploy_factory`],
/// then BIRTHS a child via `create_cell_from_factory` riding the
/// predict-then-commit spine `turn_builder`/`simulate.rs` own. The born child
/// carries the composed constraints on its `CellProgram` — a real, verified app
/// authored end-to-end. An unregistered/over-reaching factory is refused by the
/// real executor.
///
/// `agent` authorizes the birth turn; `owner` + `token` derive the child's id
/// (`CellId::derive_raw(&owner, &token)`).
#[derive(Clone, Debug)]
pub struct FactoryAuthor {
    /// The agent (cell) that authorizes the birth turn.
    pub agent: CellId,
    /// The owner public key the born child is keyed under.
    pub owner: [u8; 32],
    /// The token id the born child is keyed under (with `owner`).
    pub token: [u8; 32],
    /// The composed child cell-program (reuses `predicate_composer`'s
    /// [`Composite`] — the genuine atom algebra, never a parallel model).
    pub program: Composite,
    /// The per-epoch creation budget the authored factory advertises.
    pub creation_budget: Option<u64>,
}

impl FactoryAuthor {
    /// A fresh factory-author authorized by `agent`, birthing under
    /// `(owner, token)`, with the child program seeded by `program`.
    pub fn new(agent: CellId, owner: [u8; 32], token: [u8; 32], program: Composite) -> Self {
        FactoryAuthor {
            agent,
            owner,
            token,
            program,
            creation_budget: Some(4),
        }
    }

    /// The child id this author births (`derive_raw(owner, token)`).
    pub fn child_id(&self) -> CellId {
        CellId::derive_raw(&self.owner, &self.token)
    }

    /// The genuine [`StateConstraint`] the composed program lowers to — reuses
    /// `predicate_composer`'s [`PredicateComposer::build`] (so the SAME anti-strip
    /// / non-vacuity validation gates the child program). Fails closed on an
    /// unsafe composition.
    pub fn child_constraint(&self) -> Result<StateConstraint, GadgetError> {
        // Reuse the L2 composer's validate→lower path verbatim (agent==target
        // is immaterial here — we only want its build()).
        PredicateComposer::new(self.agent, self.agent, self.program.clone()).build()
    }

    /// The composed child [`CellProgram`] (a `Predicate([c])` of the lowered
    /// constraint — the shape `cell/src/blueprint.rs`'s settlement programs use).
    pub fn child_program(&self) -> Result<CellProgram, GadgetError> {
        Ok(CellProgram::Predicate(vec![self.child_constraint()?]))
    }

    /// The authored [`FactoryDescriptor`] — a per-app, content-addressed
    /// blueprint pinning the composed child program. Content-addressed exactly
    /// as `cell/src/blueprint.rs`'s `settlement_descriptor` is: `child_program_vk`
    /// = `canonical_program_vk(program)`, a `Fixed` VK strategy, a self-cell
    /// signature cap template, the composed constraints as the perpetual caveats.
    pub fn descriptor(&self) -> Result<FactoryDescriptor, GadgetError> {
        let program = self.child_program()?;
        let child_vk = canonical_program_vk(&program);
        let CellProgram::Predicate(constraints) = program else {
            // child_program() always returns a Predicate.
            return Err(GadgetError::Lowering {
                reason: "composed child program is not a predicate".to_string(),
            });
        };
        // Derive a per-app factory VK from the composed constraints (the
        // content-address — two distinct programs get distinct factories).
        let mut hasher = blake3::Hasher::new_derive_key("dregg-starbridge:authored-factory v1");
        hasher.update(&child_vk);
        if let Some(b) = self.creation_budget {
            hasher.update(&b.to_le_bytes());
        }
        let factory_vk = *hasher.finalize().as_bytes();
        Ok(FactoryDescriptor {
            factory_vk,
            child_program_vk: Some(child_vk),
            child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(child_vk))),
            allowed_cap_templates: vec![CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            }],
            field_constraints: vec![],
            state_constraints: constraints,
            default_mode: CellMode::Hosted,
            creation_budget: self.creation_budget,
        })
    }

    /// A [`ReflectedFactory`] over the authored (not-yet-deployed) descriptor —
    /// the Presentable face the author inspects before deploying.
    pub fn reflected(&self) -> Result<ReflectedFactory, GadgetError> {
        Ok(ReflectedFactory::new(self.descriptor()?))
    }

    /// The [`FactoryCreationParams`] for the birth — the child program VK pinned
    /// by the descriptor + the deal mode, matching the deployed descriptor so the
    /// executor admits the birth. (An over-reaching params — a cap outside the
    /// template, a mismatched VK — is what the executor REFUSES.)
    fn birth_params(&self, descriptor: &FactoryDescriptor) -> FactoryCreationParams {
        FactoryCreationParams {
            mode: descriptor.default_mode.clone(),
            program_vk: descriptor.child_program_vk,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: self.owner,
        }
    }

    /// The birth [`dregg_turn::Turn`] (a single `create_cell_from_factory`
    /// effect) against an ALREADY-deployed `factory_vk` — the turn whose
    /// admission the real executor gates. Built through the world's own
    /// [`World::turn`] + the `create_cell_from_factory` helper, NOT a parallel
    /// turn type.
    ///
    /// (The factory birth carries a pinned child-program VK, a token id, and
    /// creation params that `simulate.rs`'s `IntentDraft`/`EffectKind` palette
    /// cannot express — its `CreateCellFromFactory` variant hard-codes
    /// `program_vk: None` + empty params. So the birth rides `World::turn`
    /// directly, the SAME verified executor `commit_turn`/`simulate` run; the
    /// predict path forks the live world. See the module-level report.)
    fn birth_turn(
        &self,
        world: &World,
        factory_vk: [u8; 32],
        descriptor: &FactoryDescriptor,
    ) -> dregg_turn::Turn {
        let params = self.birth_params(descriptor);
        world.turn(
            self.agent,
            vec![create_cell_from_factory(
                factory_vk, self.owner, self.token, params,
            )],
        )
    }

    /// PREDICT the birth against an already-deployed factory WITHOUT mutating the
    /// live world — forks it (the established `World::fork` predict path) and
    /// commits the birth there, returning the executor's verdict. The live world
    /// is never touched.
    pub fn predict_birth(&self, world: &World, factory_vk: [u8; 32]) -> AuthoringOutcome {
        let descriptor = match self.descriptor() {
            Ok(d) => d,
            Err(e) => {
                return AuthoringOutcome::Refused {
                    reason: format!("{e:?}"),
                };
            }
        };
        let mut fork = world.fork();
        let turn = self.birth_turn(&fork, factory_vk, &descriptor);
        self.commit_into(&mut fork, factory_vk, turn)
    }

    /// AUTHOR THE APP END-TO-END: compose the child program, DEPLOY the factory
    /// via the real [`World::deploy_factory`], then BIRTH a child via
    /// `create_cell_from_factory` through the real [`World::commit_turn`].
    /// Returns the executor's verdict. A child born under conservation through
    /// the real executor; an over-reaching / non-conserving birth REFUSED by it.
    /// Fails closed if the composed program is unsafe (nothing is deployed).
    pub fn deploy_and_birth(&self, world: &mut World) -> Result<AuthoringOutcome, GadgetError> {
        let descriptor = self.descriptor()?;
        // (1) DEPLOY into the real executor's content-addressed registry.
        let factory_vk = world.deploy_factory(descriptor.clone());
        // (2) BIRTH a child through the verified executor.
        let turn = self.birth_turn(world, factory_vk, &descriptor);
        Ok(self.commit_into(world, factory_vk, turn))
    }

    /// BIRTH a child against an EXISTING (already-deployed) `factory_vk` without
    /// re-deploying — the "second customer of the same app" path. Refused by the
    /// executor if `factory_vk` is not registered (the unregistered-factory case).
    pub fn birth_against(
        &self,
        world: &mut World,
        factory_vk: [u8; 32],
    ) -> Result<AuthoringOutcome, GadgetError> {
        let descriptor = self.descriptor()?;
        let turn = self.birth_turn(world, factory_vk, &descriptor);
        Ok(self.commit_into(world, factory_vk, turn))
    }

    /// Commit a prepared birth `turn` into `world` and map the executor's verdict
    /// into an [`AuthoringOutcome`] (the shared tail of deploy/birth/predict).
    fn commit_into(
        &self,
        world: &mut World,
        factory_vk: [u8; 32],
        turn: dregg_turn::Turn,
    ) -> AuthoringOutcome {
        match world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => AuthoringOutcome::Born {
                factory_vk,
                receipt_hash: receipt.receipt_hash(),
                child: self.child_id(),
            },
            CommitOutcome::Rejected { reason, .. } => AuthoringOutcome::Refused { reason },
            // The world is suspended (meta-debug): the turn staged, nothing was born.
            CommitOutcome::Queued { .. } => AuthoringOutcome::Refused {
                reason: "world suspended: authoring turn queued, not committed".to_string(),
            },
        }
    }
}

impl Gadget for FactoryAuthor {
    type Output = AuthoredFactory;

    /// The form: the agent + owner/token of the born child + the recursive
    /// predicate sub-gadget for the child program + the creation budget.
    fn fields(&self) -> Vec<GadgetField> {
        vec![
            GadgetField::CellPicker {
                key: "agent".to_string(),
            },
            GadgetField::HexBytes {
                key: "owner".to_string(),
                len: 32,
            },
            GadgetField::HexBytes {
                key: "token".to_string(),
                len: 32,
            },
            GadgetField::SubGadget {
                key: "program".to_string(),
                kind: crate::presentable::GadgetKind::Predicate,
            },
            GadgetField::U64 {
                key: "creation_budget".to_string(),
                min: 0,
                max: u64::MAX,
            },
        ]
    }

    /// Edit a top-level field. The child PROGRAM is edited through the recursive
    /// predicate sub-gadget (`predicate_composer`), not a flat `set`; the flat
    /// fields are the agent / owner / token / budget.
    fn set(&mut self, field: &str, v: GadgetInput) {
        match (field, v) {
            ("agent", GadgetInput::Cell(c)) => self.agent = c,
            ("owner", GadgetInput::Bytes(b)) if b.len() == 32 => {
                self.owner.copy_from_slice(&b);
            }
            ("token", GadgetInput::Bytes(b)) if b.len() == 32 => {
                self.token.copy_from_slice(&b);
            }
            ("creation_budget", GadgetInput::U64(n)) => self.creation_budget = Some(n),
            _ => {}
        }
    }

    /// Live fail-closed validation: the composed child program must be a safe
    /// (anti-strip / non-vacuous) composition — reuses `predicate_composer`'s
    /// validation verbatim (the SAME gate that protects a directly-installed
    /// caveat protects the factory's child program).
    fn validate(&self) -> GadgetValidation {
        PredicateComposer::new(self.agent, self.agent, self.program.clone())
            .validate()
            .to_gadget()
    }

    /// Materialize the authored [`FactoryDescriptor`] — fails closed if the
    /// composed program is unsafe (the descriptor never builds).
    fn build(&self) -> Result<AuthoredFactory, GadgetError> {
        match self.validate() {
            GadgetValidation::Ok => self.descriptor(),
            GadgetValidation::Invalid { reason } => Err(GadgetError::Incomplete { reason }),
        }
    }
}

// NOTE: `FactoryAuthor` deliberately implements [`Gadget`] (Output = the
// authored [`FactoryDescriptor`]) but NOT [`crate::presentable::CommittingGadget`].
// The committing trait's `to_draft → IntentDraft` cannot faithfully carry a
// factory birth: `simulate.rs`'s `EffectKind::CreateCellFromFactory` drops the
// pinned child-program VK, the token id, and the creation params (it hard-codes
// `program_vk: None`). Rather than reinvent a lossy draft, the birth rides the
// real [`World::turn`] + [`World::commit_turn`] (the SAME verified executor),
// with [`FactoryAuthor::predict_birth`] forking the world for the no-commit
// preview. The closure lane is a non-lossy `EffectKind` for factory births (a
// `simulate.rs` change — that lane's file). See the report.

// ===========================================================================
// TESTS — the model, proven gpui-free (exactly as the sibling lanes' are).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate_composer::Atom;
    use dregg_cell::field_from_u64;

    /// A one-cell world: an open agent cell that authors + births.
    fn agent_world() -> (World, CellId) {
        let mut w = World::new();
        let agent = w.genesis_cell(0x11, 0);
        (w, agent)
    }

    /// A simple, safe child program: slot 0 must be ≤ 100 (a real caveat).
    fn capped_slot_program() -> Composite {
        Composite::Leaf(Atom::FieldLte {
            index: 0,
            value: 100,
        })
    }

    // ── a composed factory deploys + a child is born under conservation ──────

    #[test]
    fn a_composed_factory_deploys_and_births_a_child_through_the_real_executor() {
        let (mut w, agent) = agent_world();
        let owner = [0xC1u8; 32];
        let token = [0u8; 32];
        let author = FactoryAuthor::new(agent, owner, token, capped_slot_program());

        let before = w.cell_count();
        let outcome = author
            .deploy_and_birth(&mut w)
            .expect("a safe composition authors + births");
        assert!(
            outcome.born(),
            "a composed factory deploys + births a child through the real executor: {outcome:?}"
        );

        // A real child cell was born under conservation (the executor committed).
        assert_eq!(
            w.cell_count(),
            before + 1,
            "the factory birthed a child cell"
        );
        let child = outcome.child().expect("a child was born");
        assert_eq!(
            child,
            CellId::derive_raw(&owner, &token),
            "the child id is derive_raw(owner, token)"
        );

        // The born child carries the COMPOSED constraints on its CellProgram —
        // the executor installed exactly the predicate the factory advertised.
        let born = w.ledger().get(&child).expect("the child is in the ledger");
        match &born.program {
            CellProgram::Predicate(cs) => {
                assert!(
                    !cs.is_empty(),
                    "the born child carries the composed perpetual caveat"
                );
            }
            other => panic!("the born child should carry a Predicate program, got {other:?}"),
        }
    }

    // ── an unregistered factory rejects ──────────────────────────────────────

    #[test]
    fn a_birth_against_an_unregistered_factory_is_refused_by_the_executor() {
        let (mut w, agent) = agent_world();
        let author = FactoryAuthor::new(agent, [0xC2u8; 32], [0u8; 32], capped_slot_program());

        // No factory deployed at this VK → the real executor refuses the birth.
        let bogus_vk = [0x99u8; 32];
        let before = w.cell_count();
        let outcome = author
            .birth_against(&mut w, bogus_vk)
            .expect("the call returns the executor's verdict");
        assert!(
            !outcome.born(),
            "a birth from an unregistered factory must be refused: {outcome:?}"
        );
        assert_eq!(
            w.cell_count(),
            before,
            "no child cell was born on the refused birth"
        );

        // The PREDICTION agrees one turn ahead (the live world untouched).
        assert!(
            !author.predict_birth(&w, bogus_vk).born(),
            "an unregistered-factory birth is predicted to refuse"
        );
    }

    // ── the predict→commit spine: the birth is the identical verified turn ───

    #[test]
    fn predict_then_commit_authors_the_identical_birth_turn() {
        let (mut w, agent) = agent_world();
        let author = FactoryAuthor::new(agent, [0xC3u8; 32], [0u8; 32], capped_slot_program());

        // Deploy first (so the factory VK is registered), then predict the birth.
        let descriptor = author.descriptor().expect("a safe composition lowers");
        let vk = w.deploy_factory(descriptor.clone());
        assert_eq!(
            vk, descriptor.factory_vk,
            "deploy returns the content-addressed VK"
        );

        // PREDICT (no commit) shows the birth would commit; the live world untouched.
        let predicted = author.predict_birth(&w, vk);
        assert!(predicted.born(), "the birth is predicted to commit");
        let before = w.cell_count();
        assert_eq!(w.height(), 0, "predict did not mutate the live world");

        // BIRTH against the already-deployed factory — the identical verified turn.
        let outcome = author.birth_against(&mut w, vk).expect("verdict");
        assert!(outcome.born(), "the birth commits: {outcome:?}");
        assert_eq!(
            w.cell_count(),
            before + 1,
            "the predicted-then-committed child is born"
        );
    }

    // ── the authored-factory Presentable reflects real blueprint state ───────

    #[test]
    fn the_authored_factory_presentation_reflects_real_descriptor_state() {
        let (w, agent) = agent_world();
        let author = FactoryAuthor::new(agent, [0xC4u8; 32], [0u8; 32], capped_slot_program());
        let refl = author.reflected().expect("the descriptor reflects");
        let ctx = PresentCtx::new(&w, agent);
        let set = refl.present(&ctx);

        // RawFields floor (reflect_factory verbatim) + Source + Invariant.
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
        let src = set
            .iter()
            .find(|p| p.kind == PresentationKind::Source)
            .expect("Source present");
        match &src.body {
            PresentationBody::Prose(p) => {
                assert!(p.contains("Hosted"), "the Source names the real mode: {p}");
                assert!(
                    p.contains("perpetual slot caveat"),
                    "the Source names inherited caveats"
                );
            }
            other => panic!("Source should be Prose, got {other:?}"),
        }
        // The Invariant face names the GENUINE composed constraint count.
        let inv = set
            .iter()
            .find(|p| p.kind == PresentationKind::Invariant)
            .expect("Invariant present");
        match &inv.body {
            PresentationBody::Prose(p) => {
                assert!(
                    p.contains("perpetual slot caveat"),
                    "Invariant readout names the caveats: {p}"
                );
            }
            other => panic!("Invariant should be Prose, got {other:?}"),
        }
    }

    // ── an unsafe composed program fails closed (never deploys) ──────────────

    #[test]
    fn an_unsafe_child_program_fails_closed_and_never_deploys() {
        let (mut w, agent) = agent_world();
        // An empty disjunction is vacuously false — the L2 validator refuses it,
        // so the factory never builds and nothing deploys.
        let author = FactoryAuthor::new(agent, [0xC5u8; 32], [0u8; 32], Composite::AnyOf(vec![]));
        assert!(
            author.validate().is_fail_closed(),
            "the unsafe program is fail-closed"
        );
        assert!(
            author.build().is_err(),
            "an unsafe composition does not build a descriptor"
        );

        let before = w.cell_count();
        assert!(
            author.deploy_and_birth(&mut w).is_err(),
            "an unsafe program never deploys"
        );
        assert_eq!(w.cell_count(), before, "no factory deployed, no child born");
    }

    // ── the settlement families present their real lifecycle + guarantee ─────

    #[test]
    fn the_settlement_families_present_their_real_state_machine_and_invariant() {
        let (w, agent) = agent_world();
        let ctx = PresentCtx::new(&w, agent);

        let escrow = SettlementFamily::Escrow(EscrowTerms {
            amount: 100,
            depositor: field_from_u64(2222),
            beneficiary: field_from_u64(1111),
            condition: field_from_u64(99),
            timeout_height: 50,
        });
        let set = escrow.present(&ctx);

        // RawFields floor + a DomainVisual state machine + the Invariant guarantee.
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
        let dv = set
            .iter()
            .find(|p| p.kind == PresentationKind::DomainVisual)
            .expect("DomainVisual present");
        match &dv.body {
            PresentationBody::StateMachine(sm) => {
                assert_eq!(sm.current, "Open");
                assert!(sm.states.iter().any(|s| s.name == "Released" && s.terminal));
                assert!(sm.states.iter().any(|s| s.name == "Refunded" && s.terminal));
            }
            other => panic!("DomainVisual should be a StateMachine, got {other:?}"),
        }
        // The Invariant reflects the GENUINE descriptor's state_constraints.
        let inv = set
            .iter()
            .find(|p| p.kind == PresentationKind::Invariant)
            .expect("Invariant present");
        match &inv.body {
            PresentationBody::Prose(p) => assert!(
                p.contains("conserves value") && p.contains("perpetual slot caveat"),
                "the Invariant speaks the real settlement guarantee: {p}"
            ),
            other => panic!("Invariant should be Prose, got {other:?}"),
        }

        // The family lowers to the GENUINE per-deal factory descriptor.
        let d = escrow
            .descriptor()
            .expect("a valid escrow lowers to a descriptor");
        assert!(
            !d.state_constraints.is_empty(),
            "the escrow descriptor carries the proven caveats"
        );
        assert_eq!(d.default_mode, CellMode::Hosted);
    }

    // ── a settlement family can be deployed + birth a real child cell ────────

    #[test]
    fn a_settlement_family_descriptor_deploys_and_births_a_child() {
        let (mut w, agent) = agent_world();
        let bridge = SettlementFamily::Bridge(BridgeTerms {
            amount: 250,
            originator: field_from_u64(7),
            pot: field_from_u64(8),
            finality_witness: field_from_u64(42),
            timeout_height: 0,
        });
        let descriptor = bridge.descriptor().expect("the bridge lowers");
        let vk = w.deploy_factory(descriptor.clone());

        // Birth a child of this real settlement factory through the executor.
        let owner = [0xB0u8; 32];
        let token = [0u8; 32];
        let params = FactoryCreationParams {
            mode: descriptor.default_mode.clone(),
            program_vk: descriptor.child_program_vk,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        let before = w.cell_count();
        let turn = w.turn(
            agent,
            vec![create_cell_from_factory(vk, owner, token, params)],
        );
        assert!(
            w.commit_turn(turn).is_committed(),
            "a settlement-family child is born under conservation through the real executor"
        );
        assert_eq!(
            w.cell_count(),
            before + 1,
            "the bridge factory birthed a deal cell"
        );

        // The born deal cell carries the bridge's proven state constraints.
        let child = CellId::derive_raw(&owner, &token);
        let born = w.ledger().get(&child).expect("the deal cell exists");
        match &born.program {
            CellProgram::Predicate(cs) => {
                assert!(!cs.is_empty(), "the deal cell carries its caveats")
            }
            other => panic!("the deal cell should carry a Predicate program, got {other:?}"),
        }
    }

    // ── a malformed deal (zero condition) fails closed in the blueprint ──────

    #[test]
    fn a_malformed_settlement_deal_fails_closed() {
        // A zero escrow condition is rejected by the GENUINE blueprint (the
        // ZeroCondition refusal) — surfaced through our lowering, never papered over.
        let escrow = SettlementFamily::Escrow(EscrowTerms {
            amount: 100,
            depositor: field_from_u64(2222),
            beneficiary: field_from_u64(1111),
            condition: field_from_u64(0), // zero → refused
            timeout_height: 50,
        });
        assert!(
            escrow.descriptor().is_err(),
            "a zero-condition escrow is refused by the blueprint"
        );
    }
}
