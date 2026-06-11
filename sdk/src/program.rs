//! # Cell-program sugar — the constraint language at the builder surface.
//!
//! A cell's law is its installed [`CellProgram`]: the `StateConstraint` set a
//! factory bakes into every cell it births, re-evaluated by the executor on
//! EVERY turn that touches the cell. This module makes the language — in
//! particular the **turn-context actor atoms** (`docs/CELL-PROGRAM-LANGUAGE.md`
//! §3: sender bindings, own-balance bounds, the composable preimage gate) —
//! reachable from the SDK without spelling `dregg_cell::program` paths:
//!
//! ```no_run
//! use dregg_sdk::program::{self, CellProgramBuilder};
//!
//! # let owner_pk = [0u8; 32]; let controller_pk = [9u8; 32];
//! let plan = CellProgramBuilder::new()
//!     .require(program::write_once(0))            // slot 0 set at most once
//!     .require(program::sender_is(controller_pk)) // only this key may act
//!     .require(program::balance_gte(100))         // solvency floor
//!     .plan(owner_pk, [1u8; 32], /* operator */ Default::default(),
//!           /* funder */ Default::default(), /* endowment */ 500);
//! // deploy plan.descriptor, then drive the create/fund/adopt turns through
//! // runtime.turn().effects(plan.create_effects).sign()?.submit()
//! ```
//!
//! The safety is NOT in this builder — it is in the executor's program gate.
//! What the builder adds is the one sensible way to publish a custom program
//! as a content-addressed factory and birth a cell under it.

use dregg_cell::factory::{CapTarget, CapTemplate, ChildVkStrategy, canonical_program_vk};
use dregg_cell::{AuthRequired, CellMode, CellProgram, FactoryDescriptor};

use crate::polis::GovernanceCellPlan;

// The constraint language itself, re-exported whole: the outer enum, the
// composable simple atoms (`AnyOf` / `Not` / `implies` operands — including
// the actor atoms `SenderIs`, `SenderInSlot`, `BalanceGte`, `BalanceLte`,
// `PreimageGate`), and the preimage hash kinds.
pub use dregg_cell::program::{HashKind, SimpleStateConstraint, StateConstraint};
pub use dregg_cell::{field_from_u64, state::FieldElement};

// ─── atom constructors (top-level constraints) ───

/// The turn's sender must be exactly `pk` (actor binding, literal form).
/// Fail-closed: a turn with no sender context is rejected, not passed.
pub fn sender_is(pk: [u8; 32]) -> StateConstraint {
    StateConstraint::SenderIs { pk }
}

/// The turn's sender must equal the 32-byte identity stored in slot
/// `index` — the dynamic-owner actor binding (pin the slot with
/// [`write_once`] / [`immutable`] and the cell carries its own controller).
pub fn sender_in_slot(index: u8) -> StateConstraint {
    StateConstraint::SenderInSlot { index }
}

/// Post-turn own-balance floor (`balance >= min`): solvency floors,
/// fee-reserve guards.
pub fn balance_gte(min: u64) -> StateConstraint {
    StateConstraint::BalanceGte { min }
}

/// Post-turn own-balance ceiling (`balance <= max`). `balance_lte(0)` under
/// a terminal-state guard is the "resolve drains everything" tooth.
pub fn balance_lte(max: u64) -> StateConstraint {
    StateConstraint::BalanceLte { max }
}

/// Knowledge gate: the turn must exhibit a witness whose `hash_kind`-hash
/// equals the commitment stored in slot `commitment_index`.
pub fn preimage_gate(commitment_index: u8, hash_kind: HashKind) -> StateConstraint {
    StateConstraint::PreimageGate {
        commitment_index,
        hash_kind,
    }
}

/// Slot `index` may never change once the cell is born.
pub fn immutable(index: u8) -> StateConstraint {
    StateConstraint::Immutable { index }
}

/// Slot `index` may be written at most once (from zero).
pub fn write_once(index: u8) -> StateConstraint {
    StateConstraint::WriteOnce { index }
}

// ─── simple-atom constructors (for composition under AnyOf / Not / implies) ───

/// [`sender_is`] as a composable simple atom — e.g. the per-slot actor
/// binding `any_of([simple::immutable? ...])`; see
/// [`SimpleStateConstraint::implies`].
pub mod simple {
    pub use dregg_cell::program::SimpleStateConstraint;

    use super::HashKind;

    /// See [`super::sender_is`].
    pub fn sender_is(pk: [u8; 32]) -> SimpleStateConstraint {
        SimpleStateConstraint::SenderIs { pk }
    }
    /// See [`super::sender_in_slot`].
    pub fn sender_in_slot(index: u8) -> SimpleStateConstraint {
        SimpleStateConstraint::SenderInSlot { index }
    }
    /// See [`super::balance_gte`].
    pub fn balance_gte(min: u64) -> SimpleStateConstraint {
        SimpleStateConstraint::BalanceGte { min }
    }
    /// See [`super::balance_lte`].
    pub fn balance_lte(max: u64) -> SimpleStateConstraint {
        SimpleStateConstraint::BalanceLte { max }
    }
    /// See [`super::preimage_gate`].
    pub fn preimage_gate(commitment_index: u8, hash_kind: HashKind) -> SimpleStateConstraint {
        SimpleStateConstraint::PreimageGate {
            commitment_index,
            hash_kind,
        }
    }
}

/// `AnyOf` over simple atoms (the disjunction the per-slot actor binding
/// uses: `any_of([simple-immutable-guard, simple::sender_is(member)])`).
pub fn any_of(variants: Vec<SimpleStateConstraint>) -> StateConstraint {
    StateConstraint::AnyOf { variants }
}

// ─── the programmed-cell plan builder (the `.program(p)` sugar) ───

/// Build a content-addressed factory descriptor for a custom program.
///
/// The descriptor publishes `constraints` as the perpetual slot caveats of
/// every cell it births (the executor installs them as the cell's
/// [`CellProgram`] for life), with the standard one-cell budget and the
/// self-cap template the adopt bootstrap uses. Anyone can recompute the
/// descriptor from the published constraints and verify a cell's law.
pub fn programmed_cell_descriptor(constraints: Vec<StateConstraint>) -> FactoryDescriptor {
    let program = CellProgram::Predicate(constraints.clone());
    let child_vk = canonical_program_vk(&program);
    let mut hasher = blake3::Hasher::new_derive_key("dregg-sdk:programmed-cell-factory v1");
    let encoded = postcard::to_allocvec(&constraints).unwrap_or_default();
    hasher.update(&(encoded.len() as u64).to_le_bytes());
    hasher.update(&encoded);
    let factory_vk = *hasher.finalize().as_bytes();
    FactoryDescriptor {
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
        creation_budget: Some(1),
    }
}

/// Stage a custom cell program, then publish it as a factory + bootstrap
/// plan. The `.program(p)` sugar: accepts whole constraint lists or grows
/// one atom at a time via [`require`](Self::require).
#[derive(Clone, Debug, Default)]
pub struct CellProgramBuilder {
    constraints: Vec<StateConstraint>,
}

impl CellProgramBuilder {
    /// Start an empty program (an empty program constrains nothing — add
    /// atoms or the cell is law-free).
    pub fn new() -> Self {
        Self::default()
    }

    /// Add one constraint atom.
    pub fn require(mut self, constraint: StateConstraint) -> Self {
        self.constraints.push(constraint);
        self
    }

    /// Add a whole constraint list (e.g. a blueprint's published set).
    pub fn program(mut self, constraints: impl IntoIterator<Item = StateConstraint>) -> Self {
        self.constraints.extend(constraints);
        self
    }

    /// The staged constraint set.
    pub fn constraints(&self) -> &[StateConstraint] {
        &self.constraints
    }

    /// Publish as a content-addressed [`FactoryDescriptor`].
    pub fn descriptor(self) -> FactoryDescriptor {
        programmed_cell_descriptor(self.constraints)
    }

    /// Publish AND plan the bootstrap: descriptor + the create / fund /
    /// adopt turns ([`GovernanceCellPlan`], the same lifecycle as the
    /// [`crate::factories`] / [`crate::polis`] builders — deploy the
    /// descriptor, then drive the three turns through
    /// `runtime.turn().effects(..)`).
    pub fn plan(
        self,
        owner_pubkey: [u8; 32],
        token_id: [u8; 32],
        operator: dregg_cell::CellId,
        funder: dregg_cell::CellId,
        endowment: u64,
    ) -> GovernanceCellPlan {
        crate::polis::bootstrap_plan(
            self.descriptor(),
            owner_pubkey,
            token_id,
            operator,
            funder,
            endowment,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The descriptor is content-addressed: same program → same factory_vk;
    /// different program → different factory_vk AND different child VK.
    #[test]
    fn programmed_descriptor_is_content_addressed() {
        let a = programmed_cell_descriptor(vec![sender_is([1u8; 32]), balance_gte(10)]);
        let a2 = programmed_cell_descriptor(vec![sender_is([1u8; 32]), balance_gte(10)]);
        let b = programmed_cell_descriptor(vec![sender_is([2u8; 32]), balance_gte(10)]);
        assert_eq!(a.factory_vk, a2.factory_vk);
        assert_ne!(a.factory_vk, b.factory_vk);
        assert_ne!(a.child_program_vk, b.child_program_vk);
        assert_eq!(a.state_constraints.len(), 2);
    }

    /// The builder sugar produces the same descriptor as the direct fn.
    #[test]
    fn builder_matches_direct_descriptor() {
        let direct = programmed_cell_descriptor(vec![write_once(0), sender_in_slot(1)]);
        let built = CellProgramBuilder::new()
            .require(write_once(0))
            .require(sender_in_slot(1))
            .descriptor();
        assert_eq!(direct.factory_vk, built.factory_vk);
        assert_eq!(direct.hash(), built.hash());
    }
}
