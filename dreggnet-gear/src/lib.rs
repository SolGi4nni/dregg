//! # `dreggnet-gear` — equippable, cross-cell-owned GEAR + class-gated TALENTS.
//!
//! Progression roadmap #2–3 (`docs/GAME-INFRA-ROADMAP.md`), built additively on the real
//! substrate. Two deliverables, each an executor-refereed kernel predicate:
//!
//! ## [`gear`] — GEAR gated CROSS-CELL by real ownership
//!
//! A piece of gear is an owned [`dreggnet_asset`] note carrying a content-addressed
//! stat/trait block ([`statblock`]); its rarity + traits are committed into the
//! [`dreggnet_asset::AssetId`] via the traits_root mint seed. EQUIPPING gates a
//! run/character-cell ability on OWNING + equipping the PEER gear cell, via the real
//! `multicell` [`StateConstraint::ObservedFieldEquals`](dregg_app_framework::StateConstraint)
//! cross-cell primitive — "the flaming-sword ability unlocks BECAUSE you own+equip it at a
//! finalized root" is a KERNEL predicate, not a client `if`. A NON-OWNER cannot equip (the
//! asset signature gate refuses the ownership proof); the ability is REFUSED before equip
//! and COMMITS after; a spoofed equip (un-equipped / divergent value / stripped witness) is
//! REFUSED. Gear PERSISTS across runs (the asset lineage). Durability is an optional
//! `Monotonic` wear sink.
//!
//! ## [`talents`] — class-gated spells WIRED + an echoes-gated tree
//!
//! The built-but-idle `spells.rs` spellbook is wired into play so a **Mage run != a
//! Warrior run** (each spell is class-locked on the `WriteOnce` class field). A TALENT TREE
//! extends `meta.rs`: each talent is an echoes-gated `FieldGte(echoes, price)` +
//! `WriteOnce` boon, some prereq- or class-gated. Talents cost DEATH-EARNED echoes, never
//! $DREGG — the no-pay-to-win line, enforced by construction (no dregg field/method exists).
//!
//! ## The edge (sober)
//!
//! Your loadout is provable and un-dupable; "own AND equip to use" is enforced ACROSS cells
//! by the kernel (stronger than any single-cell `if`); build diversity is real (a Mage
//! genuinely cannot cast a Warrior's spell, and vice versa); and power is earned, not
//! bought. Everything is DRIVEN on the real executor (see each module's tests), never LARPed.

pub mod gear;
pub mod statblock;
pub mod talents;

pub use gear::{Armory, EquipError, EquipGate, Gear, Loadout};
pub use statblock::{GearSlot, Rarity, StatBlock};
pub use talents::{ClassRun, TALENT_TREE, Talent};
