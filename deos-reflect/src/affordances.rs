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

use dregg_cell::{AuthRequired, is_attenuation};
use dregg_turn::action::Effect;
use dregg_types::CellId;

/// One affordance — a named message a cell understands. The viewer must HOLD at
/// least `required` authority to see/fire it; firing runs `effect_template` (a real
/// [`dregg_turn::Effect`], the turn the embedded executor runs).
#[derive(Clone, Debug)]
pub struct Affordance {
    /// The operation name (unique within its surface).
    pub name: String,
    /// The authority a viewer must HOLD: the gate is `is_attenuation(held, required)`
    /// = `required ⊆ held`. A `None` requirement is always satisfiable.
    pub required: AuthRequired,
    /// The effect this affordance fires (a real `Effect`, not a stub).
    pub effect_template: Effect,
}

impl Affordance {
    pub fn new(name: impl Into<String>, required: AuthRequired, effect_template: Effect) -> Self {
        Affordance {
            name: name.into(),
            required,
            effect_template,
        }
    }

    /// **THE CAP-GATE** — is this affordance authorized for a holder of `held`?
    ///
    /// `is_attenuation(held, required)` = `required ⊆ held` (the proven attenuation
    /// lattice). `None` is always satisfiable (the cap-badge inversion: `None` is the
    /// TOP of the lattice as a *requirement*, so a `None`-gated message is open to
    /// everyone; the real guarantee fires in the EXECUTOR, not here).
    pub fn authorized_for(&self, held: &AuthRequired) -> bool {
        if matches!(self.required, AuthRequired::None) {
            return true;
        }
        is_attenuation(held, &self.required)
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
