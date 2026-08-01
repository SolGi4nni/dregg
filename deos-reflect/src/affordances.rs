//! THE AFFORDANCE SURFACE — a cell's published, cap-gated message set, projected
//! per-viewer by the proven attenuation lattice.
//!
//! A cell exposes a set of named [`Affordance`]s (the deos analogue of a server's
//! htmx endpoints). Each carries the `required` authority a viewer must HOLD to
//! see/fire it; [`AffordanceSurface::project_for`] filters by `is_attenuation`
//! (`required ⊆ held`). A weaker viewer sees fewer; an admin sees more; lacking
//! authority → the affordance is simply absent.
//!
//! Ported from starbridge-v2's gpui-free `affordance.rs`, but **decoupled from the
//! window `SurfaceCapability`**: the held authority is a bare `AuthRequired` (the
//! same the executor's cap-gate and `deos-js`'s applet already speak), so the
//! projection is reusable over the substance, not the cockpit window stack.

use dregg_cell::{AuthRequired, Requirement};
use dregg_turn::action::Effect;
use dregg_types::CellId;

/// One affordance — a named message a cell understands. The viewer must HOLD at
/// least `required` authority to see/fire it; firing runs `effect_template` (a real
/// [`dregg_turn::Effect`], the turn the embedded executor runs).
#[derive(Clone, Debug)]
pub struct Affordance {
    /// The operation name (unique within its surface).
    pub name: String,
    /// The authority a viewer must HOLD, as a [`Requirement`] — the intent is on
    /// the face of the value ([`Requirement::Public`] = ungated,
    /// `AtLeast(c)` = `c ⊆ held`, [`Requirement::Root`] = the lattice top only).
    pub required: Requirement,
    /// The effect this affordance fires (a real `Effect`, not a stub).
    pub effect_template: Effect,
}

impl Affordance {
    pub fn new(name: impl Into<String>, required: Requirement, effect_template: Effect) -> Self {
        Affordance {
            name: name.into(),
            required,
            effect_template,
        }
    }

    /// **THE CAP-GATE** — is this affordance authorized for a holder of `held`?
    ///
    /// [`Requirement::satisfied_by`] — the ONE decision function, the same call every
    /// other affordance gate in the workspace makes. This crate used to special-case
    /// `AuthRequired::None => true` while `starbridge-web-surface` and
    /// `app-framework` read the same value as root-only; `Requirement` splits those
    /// into [`Requirement::Public`] and [`Requirement::Root`] so there is nothing
    /// left to disagree about.
    pub fn authorized_for(&self, held: &AuthRequired) -> bool {
        self.required.satisfied_by(held)
    }

    /// A stable, `Eq`-able summary of the effect template (the `Effect` enum is not
    /// `PartialEq`).
    pub fn effect_summary(&self) -> EffectSummary {
        EffectSummary::of(&self.effect_template)
    }
}

/// A cell's published affordance surface — the messages it exposes.
#[derive(Clone, Debug)]
pub struct AffordanceSurface {
    /// The cell backing this surface.
    pub cell: CellId,
    /// The declared affordances (names unique; a duplicate `declare` replaces).
    pub affordances: Vec<Affordance>,
}

impl AffordanceSurface {
    pub fn new(cell: CellId) -> Self {
        AffordanceSurface {
            cell,
            affordances: Vec::new(),
        }
    }

    /// Declare an affordance (replacing any prior one of the same name).
    pub fn declare(mut self, aff: Affordance) -> Self {
        self.affordances.retain(|a| a.name != aff.name);
        self.affordances.push(aff);
        self
    }

    /// Every declared affordance name (unfiltered).
    pub fn all_names(&self) -> Vec<String> {
        self.affordances.iter().map(|a| a.name.clone()).collect()
    }

    /// Look up an affordance by name.
    pub fn get(&self, name: &str) -> Option<&Affordance> {
        self.affordances.iter().find(|a| a.name == name)
    }

    /// **PROJECT FOR A VIEWER** — the cap-gated set the holder of `held` may see/fire.
    /// The frustum's affordance half: a weaker viewer receives a strictly smaller set.
    pub fn project_for(&self, held: &AuthRequired) -> Vec<&Affordance> {
        self.affordances
            .iter()
            .filter(|a| a.authorized_for(held))
            .collect()
    }

    /// The names the holder of `held` may see/fire (the projected surface, by name).
    pub fn visible_names(&self, held: &AuthRequired) -> Vec<String> {
        self.project_for(held)
            .into_iter()
            .map(|a| a.name.clone())
            .collect()
    }
}

/// A stable, comparable readout of a real [`Effect`] template (the `Effect` enum is
/// not `PartialEq`) — its variant + the principal cell(s) it acts on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectSummary {
    SetField {
        cell: CellId,
        index: u64,
    },
    Transfer {
        from: CellId,
        to: CellId,
        amount: u64,
    },
    GrantCapability {
        from: CellId,
        to: CellId,
    },
    RevokeCapability {
        cell: CellId,
        slot: u32,
    },
    EmitEvent {
        cell: CellId,
    },
    IncrementNonce {
        cell: CellId,
    },
    Other {
        tag: &'static str,
    },
}

impl EffectSummary {
    pub fn of(effect: &Effect) -> EffectSummary {
        match effect {
            Effect::SetField { cell, index, .. } => EffectSummary::SetField {
                cell: *cell,
                index: *index,
            },
            Effect::Transfer { from, to, amount } => EffectSummary::Transfer {
                from: *from,
                to: *to,
                amount: *amount,
            },
            Effect::GrantCapability { from, to, .. } => EffectSummary::GrantCapability {
                from: *from,
                to: *to,
            },
            Effect::RevokeCapability { cell, slot } => EffectSummary::RevokeCapability {
                cell: *cell,
                slot: *slot,
            },
            Effect::EmitEvent { cell, .. } => EffectSummary::EmitEvent { cell: *cell },
            Effect::IncrementNonce { cell } => EffectSummary::IncrementNonce { cell: *cell },
            other => EffectSummary::Other {
                tag: effect_variant_tag(other),
            },
        }
    }
}

/// The static variant tag of a real [`Effect`].
fn effect_variant_tag(effect: &Effect) -> &'static str {
    match effect {
        Effect::SetField { .. } => "SetField",
        Effect::Transfer { .. } => "Transfer",
        Effect::GrantCapability { .. } => "GrantCapability",
        Effect::RevokeCapability { .. } => "RevokeCapability",
        Effect::EmitEvent { .. } => "EmitEvent",
        Effect::IncrementNonce { .. } => "IncrementNonce",
        Effect::CreateCell { .. } => "CreateCell",
        Effect::Burn { .. } => "Burn",
        Effect::CellSeal { .. } => "CellSeal",
        Effect::CellUnseal { .. } => "CellUnseal",
        Effect::CellDestroy { .. } => "CellDestroy",
        Effect::CreateCellFromFactory { .. } => "CreateCellFromFactory",
        Effect::MakeSovereign { .. } => "MakeSovereign",
        _ => "OtherEffect",
    }
}

#[cfg(test)]
mod gate_oracle_tests {
    use super::*;
    use dregg_cell::Credential;
    use dregg_types::CellId;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    fn all_requirements() -> Vec<Requirement> {
        vec![
            Requirement::Public,
            Requirement::AtLeast(Credential::Signature),
            Requirement::AtLeast(Credential::Proof),
            Requirement::AtLeast(Credential::Either),
            Requirement::AtLeast(Credential::Custom { vk_hash: [3u8; 32] }),
            Requirement::Root,
            Requirement::Never,
        ]
    }

    fn all_held() -> Vec<AuthRequired> {
        vec![
            AuthRequired::None,
            AuthRequired::Signature,
            AuthRequired::Proof,
            AuthRequired::Either,
            AuthRequired::Impossible,
            AuthRequired::Custom { vk_hash: [3u8; 32] },
        ]
    }

    #[test]
    fn the_cap_gate_is_exactly_the_one_requirement_decision_function() {
        // THE ORACLE. This crate's gate must return what `Requirement::satisfied_by`
        // returns — for EVERY requirement shape against EVERY holding. This crate is
        // one of the two that special-cased `AuthRequired::None => true` while three
        // others read it as root-only.
        let cell = cid(0x11);
        for required in all_requirements() {
            for held in all_held() {
                let aff = Affordance::new("op", required.clone(), Effect::IncrementNonce { cell });
                assert_eq!(
                    aff.authorized_for(&held),
                    required.satisfied_by(&held),
                    "the reflect gate diverged from Requirement::satisfied_by \
                     for required={required:?} held={held:?}"
                );
            }
        }
    }

    #[test]
    fn root_public_and_never_admit_independently_known_holder_sets() {
        let cell = cid(0x12);
        let admitted = |req: Requirement| -> Vec<AuthRequired> {
            let aff = Affordance::new("op", req, Effect::IncrementNonce { cell });
            all_held()
                .into_iter()
                .filter(|h| aff.authorized_for(h))
                .collect()
        };
        assert_eq!(admitted(Requirement::Root), vec![AuthRequired::None]);
        assert_eq!(admitted(Requirement::Public), all_held());
        assert!(admitted(Requirement::Never).is_empty());
        assert_eq!(
            admitted(Requirement::AtLeast(Credential::Signature)),
            vec![
                AuthRequired::None,
                AuthRequired::Signature,
                AuthRequired::Either
            ]
        );
    }
}
