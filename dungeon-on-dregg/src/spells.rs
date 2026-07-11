//! # `spells` — class-locked, mana-costed abilities as executor-enforced turns
//!
//! A spell in a class RPG is `only <class> may cast it`, `it costs mana`, `it has an
//! effect`. This module makes all three a REAL dregg tooth on a spellcaster cell —
//! the referee is the kernel, not the game code:
//!
//! - **Class-locked.** Each spell's case carries
//!   [`FieldEquals`](StateConstraint::FieldEquals)`{ class, <required class> }` — the
//!   exact class-gate [`crate::progression`]'s arcane bolt uses. A Warrior driving the
//!   Mage's Fireball fails this and is a REAL
//!   [`WorldError::Refused`](spween_dregg::WorldError) — nothing commits.
//! - **Mana-costed.** `mana_spent` is a [`Monotonic`](StateConstraint::Monotonic)
//!   accumulator; `mana_budget` is a [`WriteOnce`](StateConstraint::WriteOnce) pool
//!   ceiling. Every spell case carries
//!   [`FieldLteField`](StateConstraint::FieldLteField)`{ mana_spent, mana_budget }` —
//!   a cast that would push cumulative spend past the pool is a REAL executor refusal
//!   (an overspend never commits). This is the storage-mandate budget tooth
//!   (`spent <= ceiling`) applied to mana.
//! - **An effect.** A cast writes a real field: damage into a
//!   [`StrictMonotonic`](StateConstraint::StrictMonotonic) [`DAMAGE_SLOT`], a heal
//!   into [`HP_SLOT`], a buff into [`BUFF_SLOT`].
//!
//! ## The spellbook
//!
//! Four spells across the three [`crate::progression`] classes, exhibiting each
//! effect kind and both refusal teeth:
//!
//! | spell     | class     | cost | effect       |
//! |-----------|-----------|------|--------------|
//! | Fireball  | [`MAGE`]  | 4    | damage +8    |
//! | Mend      | [`MAGE`]  | 3    | heal +6      |
//! | Rally     | [`WARRIOR`] | 2  | buff +1      |
//! | Backstab  | [`ROGUE`] | 2    | damage +5    |
//!
//! [`MAGE`]: crate::progression::MAGE
//! [`WARRIOR`]: crate::progression::WARRIOR
//! [`ROGUE`]: crate::progression::ROGUE
//!
//! ## Honest scope
//!
//! - REAL committed cell state; casts are REAL turns; the class-gate, mana-gate and
//!   effect writes are REAL executor-enforced `StateConstraint`s (driven non-vacuously
//!   in [`mod tests`]: a wrong-class cast and an over-budget cast are real refusals
//!   that commit nothing; the valid cast commits with the effect and the receipts
//!   chain).
//! - A SINGLE spellcaster cell — one serial writer under one owner key. Cost/effect
//!   numbers are design params; the TEETH guarantee the invariants (only the right
//!   class casts, cumulative spend never passes the pool, the effect is a real write).

use dregg_app_framework::{
    CellProgram, Effect, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    field_from_u64, symbol,
};
use dregg_cell::program::SimpleStateConstraint;
use spween_dregg::{CompiledStory, WorldCell, WorldError};
use std::sync::Arc;

use crate::progression::{MAGE, ROGUE, WARRIOR};

// ── The spellcaster cell's slot layout ───────────────────────────────────────────

/// `class` — the caster's class id ([`WARRIOR`]/[`MAGE`]/[`ROGUE`]).
/// [`WriteOnce`](StateConstraint::WriteOnce): set once at creation, then frozen.
pub const CLASS_SLOT: u8 = 1;
/// `mana_spent` — the cumulative mana spent. [`Monotonic`](StateConstraint::Monotonic):
/// never rewound; bounded by the pool via [`FieldLteField`](StateConstraint::FieldLteField).
pub const MANA_SPENT_SLOT: u8 = 2;
/// `mana_budget` — the mana pool ceiling. [`WriteOnce`](StateConstraint::WriteOnce):
/// seeded at creation. The mana-gate enforces `mana_spent <= mana_budget`.
pub const MANA_BUDGET_SLOT: u8 = 3;
/// `hp` — the caster's health (a heal's target). Seeded at creation, raised by a heal.
pub const HP_SLOT: u8 = 4;
/// `buff` — a [`StrictMonotonic`](StateConstraint::StrictMonotonic) buff counter (a
/// buff spell's effect).
pub const BUFF_SLOT: u8 = 5;
/// `damage` — a [`StrictMonotonic`](StateConstraint::StrictMonotonic) accumulator of
/// damage dealt (a damage spell's effect).
pub const DAMAGE_SLOT: u8 = 6;

/// The method the creation turn presents (writes `class`, `mana_budget`, `hp`).
pub const CREATE_CASTER_METHOD: &str = "caster/create";

/// The scene id driving the spellcaster cell's deterministic identity.
pub const CASTER_SCENE_ID: &str = "dungeon-on-dregg/spellcaster/v1";

// ── The spellbook ────────────────────────────────────────────────────────────────

/// A spell's effect — a real field write the cast performs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpellEffect {
    /// Deal `amount` damage: advance [`DAMAGE_SLOT`] (`StrictMonotonic`).
    Damage(u64),
    /// Heal `amount` HP: raise [`HP_SLOT`] (`StrictMonotonic`).
    Heal(u64),
    /// Apply a buff: advance [`BUFF_SLOT`] by `amount` (`StrictMonotonic`).
    Buff(u64),
}

impl SpellEffect {
    /// The slot this effect writes.
    fn slot(&self) -> u8 {
        match self {
            SpellEffect::Damage(_) => DAMAGE_SLOT,
            SpellEffect::Heal(_) => HP_SLOT,
            SpellEffect::Buff(_) => BUFF_SLOT,
        }
    }
    /// The amount this effect adds to its slot.
    fn amount(&self) -> u64 {
        match self {
            SpellEffect::Damage(a) | SpellEffect::Heal(a) | SpellEffect::Buff(a) => *a,
        }
    }
}

/// A spell: its method, the class locked to it, the mana cost, and the effect.
#[derive(Clone, Copy, Debug)]
pub struct Spell {
    /// A human name (for the example).
    pub name: &'static str,
    /// The turn method this spell presents.
    pub method: &'static str,
    /// The class allowed to cast it (the `FieldEquals(class, .)` gate).
    pub class: u64,
    /// The mana this cast spends (accrues on `mana_spent`, bounded by the pool).
    pub cost: u64,
    /// The effect (a real field write).
    pub effect: SpellEffect,
}

/// Fireball — a [`MAGE`] damage spell (cost 4, +8 damage).
pub const FIREBALL: Spell = Spell {
    name: "Fireball",
    method: "spell/fireball",
    class: MAGE,
    cost: 4,
    effect: SpellEffect::Damage(8),
};
/// Mend — a [`MAGE`] heal spell (cost 3, +6 HP).
pub const MEND: Spell = Spell {
    name: "Mend",
    method: "spell/mend",
    class: MAGE,
    cost: 3,
    effect: SpellEffect::Heal(6),
};
/// Rally — a [`WARRIOR`] buff spell (cost 2, +1 buff).
pub const RALLY: Spell = Spell {
    name: "Rally",
    method: "spell/rally",
    class: WARRIOR,
    cost: 2,
    effect: SpellEffect::Buff(1),
};
/// Backstab — a [`ROGUE`] damage spell (cost 2, +5 damage).
pub const BACKSTAB: Spell = Spell {
    name: "Backstab",
    method: "spell/backstab",
    class: ROGUE,
    cost: 2,
    effect: SpellEffect::Damage(5),
};

/// The whole spellbook (for the program builder + the example to iterate).
pub const SPELLBOOK: [Spell; 4] = [FIREBALL, MEND, RALLY, BACKSTAB];

// ── The spellcaster cell program ─────────────────────────────────────────────────

/// **Build the spellcaster cell's [`CompiledStory`]** — slot layout + the
/// executor-enforced spell program (a real [`CellProgram::Cases`]).
///
/// Cases:
/// 1. **Global invariants** (`Always`): `class` + `mana_budget` [`WriteOnce`],
///    `mana_spent` [`Monotonic`] (spend never rewinds).
/// 2. **`caster/create`**: the written class is a valid id (`AnyOf[FieldEquals(class,
///    WARRIOR|MAGE|ROGUE)]`); the global `WriteOnce` makes it a one-time move.
/// 3. **each spell** (`spell/<name>`): `FieldEquals(class, <required>)` (the class-lock)
///    + `FieldLteField(mana_spent <= mana_budget)` (the mana-gate) + `StrictMonotonic`
///    on the effect slot (the effect is a real advancing write).
pub fn caster_story() -> CompiledStory {
    let mut cases = Vec::new();

    // 1. Global invariants.
    cases.push(TransitionCase {
        guard: TransitionGuard::Always,
        constraints: vec![
            StateConstraint::WriteOnce { index: CLASS_SLOT },
            StateConstraint::WriteOnce {
                index: MANA_BUDGET_SLOT,
            },
            StateConstraint::Monotonic {
                index: MANA_SPENT_SLOT,
            },
        ],
    });

    // 2. create — the class must be a valid id (WriteOnce makes it once).
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(CREATE_CASTER_METHOD),
        },
        constraints: vec![StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: CLASS_SLOT,
                    value: field_from_u64(WARRIOR),
                },
                SimpleStateConstraint::FieldEquals {
                    index: CLASS_SLOT,
                    value: field_from_u64(MAGE),
                },
                SimpleStateConstraint::FieldEquals {
                    index: CLASS_SLOT,
                    value: field_from_u64(ROGUE),
                },
            ],
        }],
    });

    // 3. each spell — class-locked, mana-gated, with a real effect write.
    for spell in SPELLBOOK {
        cases.push(TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(spell.method),
            },
            constraints: vec![
                // THE CLASS-LOCK: only the right class may cast.
                StateConstraint::FieldEquals {
                    index: CLASS_SLOT,
                    value: field_from_u64(spell.class),
                },
                // THE MANA-GATE: cumulative spend never passes the pool.
                StateConstraint::FieldLteField {
                    left_index: MANA_SPENT_SLOT,
                    right_index: MANA_BUDGET_SLOT,
                },
                // THE EFFECT: a real advancing field write.
                StateConstraint::StrictMonotonic {
                    index: spell.effect.slot(),
                },
            ],
        });
    }

    CompiledStory {
        scene_id: CASTER_SCENE_ID.to_string(),
        var_slots: [
            ("class".to_string(), CLASS_SLOT as usize),
            ("mana_spent".to_string(), MANA_SPENT_SLOT as usize),
            ("mana_budget".to_string(), MANA_BUDGET_SLOT as usize),
            ("hp".to_string(), HP_SLOT as usize),
            ("buff".to_string(), BUFF_SLOT as usize),
            ("damage".to_string(), DAMAGE_SLOT as usize),
        ]
        .into_iter()
        .collect(),
        has_slots: Default::default(),
        passage_index: Default::default(),
        program: CellProgram::Cases(cases),
        fully_gated: Default::default(),
    }
}

/// **Deploy a fresh spellcaster** as a real world-cell. Deterministic in `seed`.
pub fn deploy_caster(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(caster_story()), seed)
        .expect("the spellcaster cell deploys")
}

/// **Create the spellcaster** — the one-time creation move writing `class`,
/// `mana_budget` (both `WriteOnce`) and starting `hp`. A rival re-creation is refused.
pub fn create_caster(
    world: &WorldCell,
    class_id: u64,
    mana_budget: u64,
    hp: u64,
) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    world.apply_raw(
        CREATE_CASTER_METHOD,
        vec![
            Effect::SetField {
                cell,
                index: CLASS_SLOT as usize,
                value: field_from_u64(class_id),
            },
            Effect::SetField {
                cell,
                index: MANA_BUDGET_SLOT as usize,
                value: field_from_u64(mana_budget),
            },
            Effect::SetField {
                cell,
                index: HP_SLOT as usize,
                value: field_from_u64(hp),
            },
        ],
    )
}

/// **Cast a spell** — a real turn under the spell's method that spends the mana
/// (`mana_spent += cost`) and applies the effect (a real field write). The executor
/// admits it IFF the caster's class matches (`FieldEquals`), the cumulative spend
/// stays within the pool (`FieldLteField`), and the effect slot strictly advances.
/// A wrong-class or over-budget cast is a real [`WorldError::Refused`] — nothing
/// commits (anti-ghost).
pub fn cast(world: &WorldCell, spell: Spell) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    let new_spent = world.read_var("mana_spent") + spell.cost;
    let effect_slot = spell.effect.slot();
    let effect_var = match spell.effect {
        SpellEffect::Damage(_) => "damage",
        SpellEffect::Heal(_) => "hp",
        SpellEffect::Buff(_) => "buff",
    };
    let new_effect = world.read_var(effect_var) + spell.effect.amount();

    world.apply_raw(
        spell.method,
        vec![
            Effect::SetField {
                cell,
                index: MANA_SPENT_SLOT as usize,
                value: field_from_u64(new_spent),
            },
            Effect::SetField {
                cell,
                index: effect_slot as usize,
                value: field_from_u64(new_effect),
            },
        ],
    )
}

/// Introspect the executor-enforced constraints installed on a method's case (proof
/// each rule is a real kernel predicate — for the example to print the teeth).
pub fn case_constraints(story: &CompiledStory, method: &str) -> Vec<StateConstraint> {
    let m = symbol(method);
    let CellProgram::Cases(cases) = &story.program else {
        return Vec::new();
    };
    cases
        .iter()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: mm } if *mm == m))
        .map(|c| c.constraints.clone())
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every spell's case carries the three real teeth: `FieldEquals(class, .)` (the
    /// class-lock), `FieldLteField(mana_spent <= mana_budget)` (the mana-gate), and a
    /// `StrictMonotonic` on the effect slot — kernel predicates, not app bookkeeping.
    #[test]
    fn every_spell_case_carries_the_class_mana_and_effect_teeth() {
        let story = caster_story();
        for spell in SPELLBOOK {
            let cs = case_constraints(&story, spell.method);
            assert!(
                cs.iter().any(|c| matches!(
                    c,
                    StateConstraint::FieldEquals { index, value }
                        if *index == CLASS_SLOT && *value == field_from_u64(spell.class)
                )),
                "{} is class-locked FieldEquals(class, {}); got {cs:?}",
                spell.name,
                spell.class
            );
            assert!(
                cs.iter().any(|c| matches!(
                    c,
                    StateConstraint::FieldLteField { left_index, right_index }
                        if *left_index == MANA_SPENT_SLOT && *right_index == MANA_BUDGET_SLOT
                )),
                "{} is mana-gated FieldLteField(spent <= budget); got {cs:?}",
                spell.name
            );
            assert!(
                cs.iter().any(|c| matches!(
                    c,
                    StateConstraint::StrictMonotonic { index } if *index == spell.effect.slot()
                )),
                "{}'s effect advances StrictMonotonic(slot {}); got {cs:?}",
                spell.name,
                spell.effect.slot()
            );
        }
    }

    /// A VALID cast commits with the effect: a Mage with mana casts Fireball — the
    /// damage slot rises by 8, the mana spend by 4, and it is a real committed turn.
    #[test]
    fn a_valid_cast_commits_with_its_effect() {
        let world = deploy_caster(20);
        create_caster(&world, MAGE, 10, 30).expect("creation commits");
        let r = cast(&world, FIREBALL).expect("a Mage with mana casts Fireball");
        assert_eq!(world.read_var("damage"), 8, "the damage effect landed");
        assert_eq!(world.read_var("mana_spent"), 4, "the mana was spent");
        assert_ne!(r.turn_hash, [0u8; 32], "a real committed turn");
    }

    /// THE CLASS-GATE (both directions, non-vacuous): a Warrior casting the Mage's
    /// Fireball is REFUSED; the Warrior's OWN Rally is ADMITTED. Same substrate, the
    /// class field the only pivot.
    #[test]
    fn a_wrong_class_cast_is_refused_the_right_class_commits() {
        let warrior = deploy_caster(21);
        create_caster(&warrior, WARRIOR, 10, 30).expect("Warrior creation");

        let refused = cast(&warrior, FIREBALL);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a Warrior casting the Mage's Fireball is refused, got {refused:?}"
        );
        assert_eq!(warrior.read_var("damage"), 0, "anti-ghost: no damage dealt");
        assert_eq!(
            warrior.read_var("mana_spent"),
            0,
            "anti-ghost: no mana spent"
        );

        cast(&warrior, RALLY).expect("a Warrior may cast Rally");
        assert_eq!(warrior.read_var("buff"), 1, "the buff landed");
        assert_eq!(warrior.read_var("mana_spent"), 2, "Rally's mana was spent");
    }

    /// THE MANA-GATE (non-vacuous): the SAME Fireball is REFUSED for an
    /// under-budgeted Mage (pool 3 < cost 4) and ADMITTED for one with the pool
    /// (pool 4). The mana pool the only pivot; an overspend commits nothing.
    #[test]
    fn an_over_budget_cast_is_refused_a_funded_one_commits() {
        // Pool too small for even one Fireball: the cast is refused (anti-ghost).
        let broke = deploy_caster(22);
        create_caster(&broke, MAGE, 3, 30).expect("under-funded Mage");
        let refused = cast(&broke, FIREBALL);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "casting Fireball (4) on a pool of 3 is refused, got {refused:?}"
        );
        assert_eq!(broke.read_var("mana_spent"), 0, "anti-ghost: no mana spent");
        assert_eq!(broke.read_var("damage"), 0, "anti-ghost: no damage");

        // A funded Mage casts the SAME spell.
        let funded = deploy_caster(23);
        create_caster(&funded, MAGE, 4, 30).expect("funded Mage");
        cast(&funded, FIREBALL).expect("a pool of 4 covers the cost-4 Fireball");
        assert_eq!(funded.read_var("mana_spent"), 4);
    }

    /// The mana-gate bites CUMULATIVELY: a Mage with pool 6 casts one Fireball (spend
    /// 4), then a second is REFUSED (would push cumulative spend to 8 > 6). The pool
    /// is a real cumulative budget, not a per-cast check.
    #[test]
    fn the_mana_gate_bounds_cumulative_spend() {
        let world = deploy_caster(24);
        create_caster(&world, MAGE, 6, 30).expect("Mage, pool 6");
        cast(&world, FIREBALL).expect("first Fireball (spend 4 <= 6)");
        assert_eq!(world.read_var("mana_spent"), 4);
        let refused = cast(&world, FIREBALL);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a second Fireball would spend 8 > 6 — refused, got {refused:?}"
        );
        assert_eq!(
            world.read_var("mana_spent"),
            4,
            "anti-ghost: spend unchanged"
        );
        assert_eq!(
            world.read_var("damage"),
            8,
            "anti-ghost: only the first hit"
        );
    }

    /// The three effect kinds are real field writes: Mend heals HP, Rally buffs,
    /// Fireball/Backstab damage — each a committed advancing slot.
    #[test]
    fn the_effect_kinds_are_real_field_writes() {
        let mage = deploy_caster(25);
        create_caster(&mage, MAGE, 20, 30).expect("Mage");
        cast(&mage, MEND).expect("Mend heals");
        assert_eq!(mage.read_var("hp"), 36, "Mend raised HP by 6 (30 -> 36)");
        cast(&mage, FIREBALL).expect("Fireball damages");
        assert_eq!(mage.read_var("damage"), 8);

        let rogue = deploy_caster(26);
        create_caster(&rogue, ROGUE, 20, 30).expect("Rogue");
        cast(&rogue, BACKSTAB).expect("Backstab damages");
        assert_eq!(rogue.read_var("damage"), 5);
    }

    /// CLASS and mana_budget are WriteOnce: a rival re-creation is a real refusal.
    #[test]
    fn class_and_budget_are_write_once() {
        let world = deploy_caster(27);
        create_caster(&world, MAGE, 10, 30).expect("creation commits");
        let refused = create_caster(&world, WARRIOR, 999, 1);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "re-creating the caster is refused (WriteOnce), got {refused:?}"
        );
        assert_eq!(world.read_var("class"), MAGE, "anti-ghost: still a Mage");
        assert_eq!(
            world.read_var("mana_budget"),
            10,
            "anti-ghost: pool unchanged"
        );
    }

    /// A full cast arc is a real receipt chain: create → cast → cast link
    /// `pre == prev.post` (one serial writer, one cell).
    #[test]
    fn a_cast_arc_is_a_real_receipt_chain() {
        let world = deploy_caster(28);
        let r0 = create_caster(&world, MAGE, 20, 30).expect("create");
        let r1 = cast(&world, FIREBALL).expect("Fireball");
        let r2 = cast(&world, MEND).expect("Mend");
        assert_eq!(r1.pre_state_hash, r0.post_state_hash, "chains");
        assert_eq!(r2.pre_state_hash, r1.post_state_hash, "chains");
        assert_eq!(world.read_var("damage"), 8);
        assert_eq!(world.read_var("hp"), 36);
        assert_eq!(world.read_var("mana_spent"), 7);
    }
}
