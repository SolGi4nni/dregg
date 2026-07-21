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
///    + `FieldLteField(mana_spent <= mana_budget)` (the mana-gate) + exact
///    `FieldDelta` teeth for the named spell's cost and effect amount.
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

    // The three effect slots. THE STAPLE-BINDING INVARIANT: every case must
    // CONSTRAIN each effect slot — either WRITE it (an exact `FieldDelta`) or PIN
    // it `Immutable`. Otherwise a slot whose only tooth lives under one method's
    // case is zero/writable on a DIFFERENT method's turn, and `apply_raw` lets a
    // client STAPLE `SetField(hp, +1000)` onto a legit Fireball (a free heal with
    // mana_spent 4). Default-deny already restricts a turn to the five known
    // methods; pinning the effect slots a method does NOT pay for binds every
    // hp/buff/damage change to the single method whose economics cover it.
    const EFFECT_SLOTS: [u8; 3] = [HP_SLOT, BUFF_SLOT, DAMAGE_SLOT];

    // 2. create — the class must be a valid id (WriteOnce makes it once). Creation
    // seeds `class`/`mana_budget`/`hp` and NOTHING else, so it pins every effect
    // slot it does not seed (`buff`/`damage`) and `mana_spent` Immutable: a staple
    // of a free buff/damage — or a phantom mana refund — onto the creation turn is
    // refused. (`hp` IS the creation seed — the caster's starting health, a
    // by-design one-shot genesis write frozen behind the class WriteOnce; a heal
    // AFTER creation must go through Mend, below.)
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(CREATE_CASTER_METHOD),
        },
        constraints: vec![
            StateConstraint::AnyOf {
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
            },
            StateConstraint::Immutable { index: BUFF_SLOT },
            StateConstraint::Immutable { index: DAMAGE_SLOT },
            StateConstraint::Immutable {
                index: MANA_SPENT_SLOT,
            },
        ],
    });

    // 3. each spell — class-locked, mana-gated, with a real effect write.
    for spell in SPELLBOOK {
        let written = spell.effect.slot();
        let mut constraints = vec![
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
            // Bind the method to its exact economics. A merely monotone effect
            // would accept a raw Fireball spending 1 mana for 1 damage.
            StateConstraint::FieldDelta {
                index: MANA_SPENT_SLOT,
                delta: field_from_u64(spell.cost),
            },
            StateConstraint::FieldDelta {
                index: written,
                delta: field_from_u64(spell.effect.amount()),
            },
        ];
        // PIN THE EFFECT SLOTS THIS SPELL DOES NOT WRITE. A Fireball that also
        // stapled `SetField(hp, +1000)` fails `Immutable{hp}` here; the write it
        // DOES perform (`damage`) is pinned to +8 by the `FieldDelta` above. So an
        // hp/buff/damage change can only ride the method whose mana pays for it.
        for &slot in &EFFECT_SLOTS {
            if slot != written {
                constraints.push(StateConstraint::Immutable { index: slot });
            }
        }
        cases.push(TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(spell.method),
            },
            constraints,
        });
    }

    CompiledStory {
        scene_id: CASTER_SCENE_ID.to_string(),
        var_slots: [
            ("class".to_string(), CLASS_SLOT as u64),
            ("mana_spent".to_string(), MANA_SPENT_SLOT as u64),
            ("mana_budget".to_string(), MANA_BUDGET_SLOT as u64),
            ("hp".to_string(), HP_SLOT as u64),
            ("buff".to_string(), BUFF_SLOT as u64),
            ("damage".to_string(), DAMAGE_SLOT as u64),
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
                index: CLASS_SLOT as u64,
                value: field_from_u64(class_id),
            },
            Effect::SetField {
                cell,
                index: MANA_BUDGET_SLOT as u64,
                value: field_from_u64(mana_budget),
            },
            Effect::SetField {
                cell,
                index: HP_SLOT as u64,
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
                index: MANA_SPENT_SLOT as u64,
                value: field_from_u64(new_spent),
            },
            Effect::SetField {
                cell,
                index: effect_slot as u64,
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

    /// Every spell's case carries the class-lock, mana ceiling, and exact cost/effect
    /// deltas — kernel predicates, not app bookkeeping.
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
            assert!(cs.iter().any(|c| matches!(
                c,
                StateConstraint::FieldDelta { index, delta }
                    if *index == MANA_SPENT_SLOT && *delta == field_from_u64(spell.cost)
            )));
            assert!(cs.iter().any(|c| matches!(
                c,
                StateConstraint::FieldDelta { index, delta }
                    if *index == spell.effect.slot()
                        && *delta == field_from_u64(spell.effect.amount())
            )));
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

    #[test]
    fn raw_spell_method_cannot_underpay_or_inflate_the_effect() {
        let world = deploy_caster(33);
        create_caster(&world, MAGE, 20, 30).expect("create Mage");
        let cell = world.cell_id();
        let forged = world.apply_raw(
            FIREBALL.method,
            vec![
                Effect::SetField {
                    cell,
                    index: MANA_SPENT_SLOT as u64,
                    value: field_from_u64(1),
                },
                Effect::SetField {
                    cell,
                    index: DAMAGE_SLOT as u64,
                    value: field_from_u64(1000),
                },
            ],
        );
        assert!(matches!(forged, Err(WorldError::Refused(_))));
        assert_eq!(world.read_var("mana_spent"), 0);
        assert_eq!(world.read_var("damage"), 0);

        cast(&world, FIREBALL).expect("the exact cost/effect pair commits");
        assert_eq!(world.read_var("mana_spent"), FIREBALL.cost);
        assert_eq!(world.read_var("damage"), FIREBALL.effect.amount());
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

    /// THE STAPLED-HEAL FALSIFIER (a real cell-layer hole, closed): a
    /// `SetField(hp, +1000)` heal STAPLED onto a legitimate Fireball turn cannot
    /// ride it. Before the effect slots were pinned per-method, the Fireball case
    /// constrained only `mana_spent`/`damage`; `hp` was unconstrained on that
    /// method, so a client could `apply_raw` a Fireball whose effects ALSO wrote
    /// `hp = 1030` — a free heal (30 → 1030) with mana_spent only 4. Now the
    /// Fireball case pins `Immutable{hp}`, so the stapled heal is REFUSED and
    /// nothing commits (anti-ghost). The LEGIT heal (Mend, paid) still lands.
    #[test]
    fn a_stapled_heal_cannot_ride_a_fireball() {
        let world = deploy_caster(40);
        create_caster(&world, MAGE, 10, 30).expect("create a Mage with hp 30");
        let cell = world.cell_id();

        // Staple a free heal onto an otherwise-legit Fireball (mana +4, damage +8,
        // and — the forgery — hp 30 -> 1030).
        let stapled = world.apply_raw(
            FIREBALL.method,
            vec![
                Effect::SetField {
                    cell,
                    index: MANA_SPENT_SLOT as u64,
                    value: field_from_u64(4),
                },
                Effect::SetField {
                    cell,
                    index: DAMAGE_SLOT as u64,
                    value: field_from_u64(8),
                },
                Effect::SetField {
                    cell,
                    index: HP_SLOT as u64,
                    value: field_from_u64(1030),
                },
            ],
        );
        assert!(
            matches!(stapled, Err(WorldError::Refused(_))),
            "a heal stapled onto a Fireball must be REFUSED (Immutable{{hp}}); got {stapled:?}"
        );
        // Anti-ghost: the refused turn committed NOTHING.
        assert_eq!(world.read_var("hp"), 30, "anti-ghost: hp not raised");
        assert_eq!(world.read_var("damage"), 0, "anti-ghost: no damage dealt");
        assert_eq!(world.read_var("mana_spent"), 0, "anti-ghost: no mana spent");

        // THE PIN IS NOT A BAN ON HEALING: a real, paid Mend still heals, and a
        // real Fireball still deals damage.
        cast(&world, FIREBALL).expect("a real Fireball commits");
        assert_eq!(world.read_var("damage"), 8);
        assert_eq!(world.read_var("hp"), 30, "Fireball leaves hp untouched");
        cast(&world, MEND).expect("a real, paid Mend heals");
        assert_eq!(
            world.read_var("hp"),
            36,
            "Mend raised hp by 6 (paid 3 mana)"
        );
        assert_eq!(world.read_var("mana_spent"), 7, "Fireball 4 + Mend 3");
    }

    /// The staple-binding covers ALL THREE effect slots, not just `hp`: a free
    /// `buff` stapled onto a Fireball (which does not pay for a buff) and a free
    /// `damage` stapled onto a Rally (a buff spell) are both REFUSED. Every
    /// hp/buff/damage change is bound to the one method whose mana covers it.
    #[test]
    fn a_stapled_buff_or_damage_cannot_ride_a_foreign_method() {
        // (a) buff stapled onto a Mage's Fireball — Fireball pins Immutable{buff}.
        let mage = deploy_caster(41);
        create_caster(&mage, MAGE, 20, 30).expect("create a Mage");
        let mcell = mage.cell_id();
        let buff_staple = mage.apply_raw(
            FIREBALL.method,
            vec![
                Effect::SetField {
                    cell: mcell,
                    index: MANA_SPENT_SLOT as u64,
                    value: field_from_u64(4),
                },
                Effect::SetField {
                    cell: mcell,
                    index: DAMAGE_SLOT as u64,
                    value: field_from_u64(8),
                },
                Effect::SetField {
                    cell: mcell,
                    index: BUFF_SLOT as u64,
                    value: field_from_u64(9),
                },
            ],
        );
        assert!(
            matches!(buff_staple, Err(WorldError::Refused(_))),
            "a buff stapled onto a Fireball must be REFUSED (Immutable{{buff}}); got {buff_staple:?}"
        );
        assert_eq!(mage.read_var("buff"), 0, "anti-ghost: no free buff");
        assert_eq!(mage.read_var("damage"), 0, "anti-ghost: nothing committed");

        // (b) damage stapled onto a Warrior's Rally — Rally pins Immutable{damage}.
        let warrior = deploy_caster(42);
        create_caster(&warrior, WARRIOR, 20, 30).expect("create a Warrior");
        let wcell = warrior.cell_id();
        let dmg_staple = warrior.apply_raw(
            RALLY.method,
            vec![
                Effect::SetField {
                    cell: wcell,
                    index: MANA_SPENT_SLOT as u64,
                    value: field_from_u64(2),
                },
                Effect::SetField {
                    cell: wcell,
                    index: BUFF_SLOT as u64,
                    value: field_from_u64(1),
                },
                Effect::SetField {
                    cell: wcell,
                    index: DAMAGE_SLOT as u64,
                    value: field_from_u64(500),
                },
            ],
        );
        assert!(
            matches!(dmg_staple, Err(WorldError::Refused(_))),
            "damage stapled onto a Rally must be REFUSED (Immutable{{damage}}); got {dmg_staple:?}"
        );
        assert_eq!(warrior.read_var("damage"), 0, "anti-ghost: no free damage");
        assert_eq!(warrior.read_var("buff"), 0, "anti-ghost: nothing committed");
        // The legit Rally still buffs.
        cast(&warrior, RALLY).expect("a real Rally buffs");
        assert_eq!(warrior.read_var("buff"), 1);
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
