//! # `talents` — class-gated spells WIRED into play + an echoes-gated TALENT TREE.
//!
//! Two deliverables, each a real executor tooth, so a **Mage run != a Warrior run** and
//! **talents cost death-earned echoes, never $DREGG**.
//!
//! ## 1. The wired spellbook (a Mage run != a Warrior run)
//!
//! `dungeon-on-dregg`'s [`spells`](dungeon_on_dregg::spells) module is the COMPLETE
//! class-locked, mana-costed spellbook (Fireball / Mend / Rally / Backstab) — built but
//! idle. [`ClassRun`] wires it into play: a run picks a class ([`WriteOnce`] at creation)
//! and casts. Each spell case carries `FieldEquals(class, <required>)`, so a Mage casting
//! Fireball COMMITS while a Warrior driving the SAME Fireball is a real
//! [`WorldError::Refused`](spween_dregg::WorldError) — the class field is the only pivot,
//! the referee is the kernel. Build diversity is REAL: the spells a run can cast are a
//! function of its `WriteOnce` class.
//!
//! ## 2. The talent tree (echoes-gated boons — the `meta.rs` extension)
//!
//! [`meta`](dungeon_on_dregg::meta) gives ONE echoes-bought boon. [`talent_tree_story`]
//! extends that tooth into a TREE on the SAME persistent hero cell: each [`Talent`] is a
//! `talent/claim/<name>` case carrying
//! `FieldGte(echoes, price)` + `FieldEquals(slot, 1)` + `WriteOnce(slot)`, some further
//! gated by a **prerequisite** (`FieldGte(prereq_slot, 1)` — a real tree edge) or a
//! **class** (`FieldEquals(class, <class>)` — a class-branch a wrong class can never buy).
//! Because `echoes` is [`Monotonic`](dregg_app_framework::StateConstraint::Monotonic) and
//! granted ONLY on a real death (`meta`'s `FieldEquals(dead, 1)` grant), the price is a
//! death-earned accrual THRESHOLD.
//!
//! ## No pay-to-win — BY CONSTRUCTION
//!
//! There is NO $DREGG field and NO $DREGG method on the hero cell. The ONLY input a talent
//! claim reads is the `echoes` slot, and the ONLY way to raise `echoes` is `meta`'s
//! death-gated grant. A claim below the price is refused; a forged claim under a
//! "buy-with-dregg" method default-denies; and echoes cannot be injected without a real
//! committed death. Power is earned by playing (and dying), never purchased.
//!
//! ## Honest scope — named residuals
//!
//! REAL + DRIVEN: the wired class-gated spellbook, the echoes-gated / prereq-gated /
//! class-gated talent tree, the no-P2W teeth. NAMED RESIDUALS: RESPEC (a sink that clears
//! a talent slot — needs a non-`WriteOnce` re-key path); binding a talent's EFFECT into a
//! run's starting resources (a compiler-emitted seed, as `meta` names for its boon); and
//! deeper trees (more tiers / cross-class edges) — each additive on this same tooth.

use std::sync::Arc;

use dregg_app_framework::{
    CellProgram, Effect, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    field_from_u64, symbol,
};
use spween_dregg::{CompiledStory, WorldCell, WorldError};

use dungeon_on_dregg::meta::{self, ECHOES_SLOT};
use dungeon_on_dregg::progression::{self, CLASS_SLOT, MAGE, WARRIOR};
use dungeon_on_dregg::spells::{self, Spell};

// ═══════════════════════════════════════════════════════════════════════════════
// 1. The wired spellbook — a Mage run casts what a Warrior cannot.
// ═══════════════════════════════════════════════════════════════════════════════

/// A class-picked run over the built [`spells`] spellbook. Deploying + creating fixes the
/// run's class ([`WriteOnce`]); casting is gated on it.
pub struct ClassRun {
    cell: WorldCell,
}

impl ClassRun {
    /// Start a run of `class_id` with a `mana_budget` mana pool and `hp` health — the
    /// one-time creation move (`class` + `mana_budget` are `WriteOnce`).
    pub fn start(seed: u8, class_id: u64, mana_budget: u64, hp: u64) -> Result<Self, WorldError> {
        let cell = spells::deploy_caster(seed);
        spells::create_caster(&cell, class_id, mana_budget, hp)?;
        Ok(ClassRun { cell })
    }

    /// Cast a spell — admitted IFF this run's class matches the spell's class-lock and the
    /// cumulative mana stays within the pool. A wrong-class cast is a real refusal.
    pub fn cast(&self, spell: Spell) -> Result<TurnReceipt, WorldError> {
        spells::cast(&self.cell, spell)
    }

    /// Read a cast effect / resource var (`damage` / `hp` / `buff` / `mana_spent` / `class`).
    pub fn read(&self, var: &str) -> u64 {
        self.cell.read_var(var)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// 2. The talent tree — echoes-gated boons on the persistent hero cell.
// ═══════════════════════════════════════════════════════════════════════════════

/// One node in the talent tree: its claim method + register slot, its echoes price, and
/// its optional gates (a prerequisite talent slot, and/or a required class).
#[derive(Clone, Copy, Debug)]
pub struct Talent {
    /// A human name.
    pub name: &'static str,
    /// The turn method a claim presents.
    pub method: &'static str,
    /// The `read_var` name for this talent's slot.
    pub var: &'static str,
    /// The hero-cell register slot the claim lands (`WriteOnce`).
    pub slot: u8,
    /// The accrued-echoes THRESHOLD (a `FieldGte` floor) the claim requires.
    pub price: u64,
    /// A prerequisite talent's slot (a `FieldGte(prereq, 1)` tree edge), if any.
    pub prereq_slot: Option<u8>,
    /// A required class (a `FieldEquals(class, .)` branch), if any.
    pub class: Option<u64>,
}

/// **Ironhide** — the root talent (no prereq, no class): 30 echoes.
pub const IRONHIDE: Talent = Talent {
    name: "Ironhide",
    method: "talent/claim/ironhide",
    var: "talent_ironhide",
    slot: 8,
    price: 30,
    prereq_slot: None,
    class: None,
};
/// **Deep Delver** — gated on [`IRONHIDE`] (a real tree edge): 60 echoes.
pub const DEEP_DELVER: Talent = Talent {
    name: "Deep Delver",
    method: "talent/claim/deep_delver",
    var: "talent_deep_delver",
    slot: 9,
    price: 60,
    prereq_slot: Some(IRONHIDE.slot),
    class: None,
};
/// **Arcane Mastery** — a MAGE-only branch (a Warrior can never buy it): 40 echoes.
pub const ARCANE_MASTERY: Talent = Talent {
    name: "Arcane Mastery",
    method: "talent/claim/arcane_mastery",
    var: "talent_arcane_mastery",
    slot: 10,
    price: 40,
    prereq_slot: None,
    class: Some(MAGE),
};
/// **Battle Fury** — a WARRIOR-only branch: 40 echoes.
pub const BATTLE_FURY: Talent = Talent {
    name: "Battle Fury",
    method: "talent/claim/battle_fury",
    var: "talent_battle_fury",
    slot: 11,
    price: 40,
    prereq_slot: None,
    class: Some(WARRIOR),
};

/// The whole talent tree (for the program builder + drivers to iterate).
pub const TALENT_TREE: [Talent; 4] = [IRONHIDE, DEEP_DELVER, ARCANE_MASTERY, BATTLE_FURY];

/// **Build the persistent hero cell's story WITH the talent tree installed.** Starts from
/// [`meta::meta_hero_story`] (xp / level / class / dead / echoes / boon) and ADDS, on the
/// SAME cell, for each [`Talent`]:
/// 1. a global `WriteOnce(slot)` invariant (the talent is set once, never rewritten);
/// 2. a `talent/claim/<name>` case: `FieldGte(echoes, price)` (bought with enough accrued
///    death-echoes) + any `FieldGte(prereq, 1)` (the tree edge) + any `FieldEquals(class,
///    .)` (the class branch) + `FieldEquals(slot, 1)` (lands the marker) + `WriteOnce`.
///
/// Additive to every existing progression / meta turn — a real [`CellProgram::Cases`] the
/// executor enforces move-for-move.
pub fn talent_tree_story() -> CompiledStory {
    let mut story = meta::meta_hero_story();

    // Register the talent slots so `read_var` resolves them by name.
    for t in TALENT_TREE {
        story.var_slots.insert(t.var.to_string(), t.slot as usize);
    }

    let CellProgram::Cases(cases) = &mut story.program else {
        panic!("the meta hero story is a Cases program");
    };

    // 1. Global invariant: each talent slot is WriteOnce (set once, never rewritten).
    let always = cases
        .iter_mut()
        .find(|c| matches!(c.guard, TransitionGuard::Always))
        .expect("meta_hero_story installs a global Always invariant case");
    for t in TALENT_TREE {
        always
            .constraints
            .push(StateConstraint::WriteOnce { index: t.slot });
    }

    // 2. A claim case per talent — echoes-gated, plus any prereq / class gate.
    for t in TALENT_TREE {
        let mut constraints = vec![
            // THE ECHOES GATE: bought only with enough accrued death-earned echoes.
            StateConstraint::FieldGte {
                index: ECHOES_SLOT,
                value: field_from_u64(t.price),
            },
            // Lands the talent marker, once.
            StateConstraint::FieldEquals {
                index: t.slot,
                value: field_from_u64(1),
            },
            StateConstraint::WriteOnce { index: t.slot },
        ];
        if let Some(prereq) = t.prereq_slot {
            // THE TREE EDGE: the prerequisite talent must already be held.
            constraints.push(StateConstraint::FieldGte {
                index: prereq,
                value: field_from_u64(1),
            });
        }
        if let Some(class) = t.class {
            // THE CLASS BRANCH: only the right class may buy this talent.
            constraints.push(StateConstraint::FieldEquals {
                index: CLASS_SLOT,
                value: field_from_u64(class),
            });
        }
        cases.push(TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(t.method),
            },
            constraints,
        });
    }

    story
}

/// **Deploy a persistent hero cell WITH the talent tree.** Deterministic in `seed`.
pub fn deploy_talent_hero(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(talent_tree_story()), seed)
        .expect("the talent-tree hero cell deploys")
}

/// **Claim a talent** — a real turn under the talent's `talent/claim/<name>` method
/// writing `slot = 1`. The executor GATES it on `FieldGte(echoes, price)` (+ any prereq /
/// class gate); a claim without the accrued echoes (or missing prereq / wrong class) is a
/// real [`WorldError::Refused`] that commits nothing. The `WriteOnce(slot)` makes it a
/// one-time claim.
pub fn claim_talent(world: &WorldCell, talent: Talent) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    world.apply_raw(
        talent.method,
        vec![Effect::SetField {
            cell,
            index: talent.slot as usize,
            value: field_from_u64(1),
        }],
    )
}

/// Whether `talent` is held (its slot is set).
pub fn has_talent(world: &WorldCell, talent: Talent) -> bool {
    world.read_var(talent.var) != 0
}

/// Introspect the executor-enforced constraints installed on a talent's claim case (proof
/// each rule is a real kernel predicate).
pub fn talent_constraints(story: &CompiledStory, talent: Talent) -> Vec<StateConstraint> {
    progression::case_constraints(story, talent.method)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dungeon_on_dregg::spells::{BACKSTAB, FIREBALL, RALLY};

    // ── 1. The wired spellbook — a Mage run != a Warrior run ────────────────────────

    /// A MAGE run casts what a WARRIOR run CANNOT (non-vacuous): a Mage casts Fireball
    /// (commits, +8 damage); a Warrior driving the SAME Fireball is REFUSED (class gate);
    /// and the Warrior's OWN Rally commits. Build diversity is real — the class field the
    /// only pivot.
    #[test]
    fn a_mage_run_casts_what_a_warrior_cannot() {
        let mage = ClassRun::start(40, MAGE, 20, 30).expect("mage run");
        mage.cast(FIREBALL).expect("a Mage casts Fireball");
        assert_eq!(mage.read("damage"), 8, "the Mage's Fireball landed");

        let warrior = ClassRun::start(41, WARRIOR, 20, 30).expect("warrior run");
        let refused = warrior.cast(FIREBALL);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a Warrior casting the Mage's Fireball is refused, got {refused:?}"
        );
        assert_eq!(
            warrior.read("damage"),
            0,
            "anti-ghost: the Warrior dealt no Fireball damage"
        );

        // The Warrior's own Rally commits — the same substrate, its own class's spell.
        warrior.cast(RALLY).expect("a Warrior casts Rally");
        assert_eq!(warrior.read("buff"), 1, "the Warrior's Rally landed");

        // And a Rogue's Backstab is a Rogue-only cast (a Mage can't).
        let mage2 = ClassRun::start(42, MAGE, 20, 30).expect("mage run");
        assert!(
            matches!(mage2.cast(BACKSTAB), Err(WorldError::Refused(_))),
            "a Mage casting the Rogue's Backstab is refused"
        );
    }

    // ── 2. The talent tree — echoes-gated boons ─────────────────────────────────────

    /// Every talent's claim case carries the real kernel teeth: `FieldGte(echoes, price)`,
    /// `WriteOnce(slot)`, and its prereq / class gate where declared.
    #[test]
    fn talent_cases_carry_the_real_teeth() {
        let story = talent_tree_story();
        for t in TALENT_TREE {
            let cs = talent_constraints(&story, t);
            assert!(
                cs.iter().any(|c| matches!(
                    c, StateConstraint::FieldGte { index, value }
                        if *index == ECHOES_SLOT && *value == field_from_u64(t.price)
                )),
                "{} is echoes-gated FieldGte(echoes, {}); got {cs:?}",
                t.name,
                t.price
            );
            assert!(
                cs.iter()
                    .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == t.slot)),
                "{} is WriteOnce; got {cs:?}",
                t.name
            );
            if let Some(class) = t.class {
                assert!(
                    cs.iter().any(|c| matches!(
                        c, StateConstraint::FieldEquals { index, value }
                            if *index == CLASS_SLOT && *value == field_from_u64(class)
                    )),
                    "{} is class-gated FieldEquals(class, {class}); got {cs:?}",
                    t.name
                );
            }
        }
    }

    /// Accrue enough death-echoes into a hero: choose a class, die, and grant at `depth`.
    fn dead_hero_with_echoes(seed: u8, class: u64, depth: u64) -> WorldCell {
        let world = deploy_talent_hero(seed);
        progression::choose_class(&world, class).expect("class");
        progression::perish(&world).expect("a real death");
        meta::grant_echoes(&world, depth).expect("a death funds echoes");
        world
    }

    /// THE ECHOES GATE (non-vacuous): a claim below the price is REFUSED; once enough
    /// death-echoes are accrued the SAME claim COMMITS; and the claimed talent is WriteOnce.
    #[test]
    fn a_talent_is_bought_with_enough_echoes_and_is_writeonce() {
        // A shallow death banks 15 echoes (10 + 5*1) < Ironhide's 30 → the claim is refused.
        let poor = dead_hero_with_echoes(50, MAGE, 1);
        assert!(
            meta::echoes(&poor) < IRONHIDE.price,
            "below the talent price"
        );
        let refused = claim_talent(&poor, IRONHIDE);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a claim below the echoes price is refused, got {refused:?}"
        );
        assert!(
            !has_talent(&poor, IRONHIDE),
            "anti-ghost: no talent without the echoes"
        );

        // A deeper death banks 40 echoes (10 + 5*6) >= 30 → the SAME claim commits.
        let rich = dead_hero_with_echoes(51, MAGE, 6);
        assert!(meta::echoes(&rich) >= IRONHIDE.price, "at/over the price");
        claim_talent(&rich, IRONHIDE).expect("enough echoes buys Ironhide");
        assert!(has_talent(&rich, IRONHIDE), "the talent is claimed");

        // WriteOnce: a re-claim to a different value is refused.
        let cell = rich.cell_id();
        let rewrite = rich.apply_raw(
            IRONHIDE.method,
            vec![Effect::SetField {
                cell,
                index: IRONHIDE.slot as usize,
                value: field_from_u64(2),
            }],
        );
        assert!(
            matches!(rewrite, Err(WorldError::Refused(_))),
            "rewriting a claimed talent is refused (WriteOnce), got {rewrite:?}"
        );
    }

    /// THE TREE EDGE (non-vacuous): Deep Delver requires Ironhide first. With the echoes
    /// but WITHOUT Ironhide the claim is refused; after Ironhide is held, it commits.
    #[test]
    fn a_talent_gated_on_a_prerequisite_needs_it_first() {
        // 70 echoes (10 + 5*12) covers both prices; Ironhide not yet held.
        let world = dead_hero_with_echoes(52, MAGE, 12);
        assert!(meta::echoes(&world) >= DEEP_DELVER.price);

        let refused = claim_talent(&world, DEEP_DELVER);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "Deep Delver without its prerequisite Ironhide is refused, got {refused:?}"
        );
        assert!(!has_talent(&world, DEEP_DELVER), "anti-ghost: not claimed");

        // Buy the prerequisite, then the gated talent commits.
        claim_talent(&world, IRONHIDE).expect("Ironhide first");
        claim_talent(&world, DEEP_DELVER).expect("with Ironhide held, Deep Delver commits");
        assert!(has_talent(&world, DEEP_DELVER));
    }

    /// THE CLASS BRANCH (non-vacuous): a WARRIOR with 40 echoes CANNOT buy the MAGE-only
    /// Arcane Mastery, but CAN buy the Warrior-only Battle Fury. A MAGE is the mirror image.
    #[test]
    fn a_class_gated_talent_refuses_the_wrong_class() {
        let warrior = dead_hero_with_echoes(53, WARRIOR, 6); // 40 echoes
        assert!(meta::echoes(&warrior) >= ARCANE_MASTERY.price);

        let refused = claim_talent(&warrior, ARCANE_MASTERY);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a Warrior buying the Mage-only Arcane Mastery is refused, got {refused:?}"
        );
        assert!(
            !has_talent(&warrior, ARCANE_MASTERY),
            "anti-ghost: not bought"
        );

        // The Warrior CAN buy its own Battle Fury.
        claim_talent(&warrior, BATTLE_FURY).expect("a Warrior buys Battle Fury");
        assert!(has_talent(&warrior, BATTLE_FURY));

        // And a Mage buys Arcane Mastery.
        let mage = dead_hero_with_echoes(54, MAGE, 6);
        claim_talent(&mage, ARCANE_MASTERY).expect("a Mage buys Arcane Mastery");
        assert!(has_talent(&mage, ARCANE_MASTERY));
    }

    /// NO PAY-TO-WIN — talents are death-echoes-only, never $DREGG. On a LIVING hero (no
    /// death, zero echoes): a claim is refused (FieldGte), a forged "buy with dregg" method
    /// default-denies, and echoes cannot be injected without a real death. The only path to
    /// a talent is play-then-die-then-claim.
    #[test]
    fn talents_are_echoes_only_never_dregg() {
        let world = deploy_talent_hero(55);
        progression::choose_class(&world, MAGE).expect("class");
        assert_eq!(meta::echoes(&world), 0, "a living hero has no echoes");

        // A living hero cannot claim (no accrued echoes) — FieldGte refuses.
        let no_echoes = claim_talent(&world, IRONHIDE);
        assert!(
            matches!(no_echoes, Err(WorldError::Refused(_))),
            "a claim with zero echoes is refused, got {no_echoes:?}"
        );

        // A forged "$DREGG purchase" of the talent (an unknown method) default-denies.
        let cell = world.cell_id();
        let dregg_buy = world.apply_raw(
            "shop/buy_talent_with_dregg",
            vec![Effect::SetField {
                cell,
                index: IRONHIDE.slot as usize,
                value: field_from_u64(1),
            }],
        );
        assert!(
            matches!(dregg_buy, Err(WorldError::Refused(_))),
            "buying a talent with $DREGG (an off-book method) is refused, got {dregg_buy:?}"
        );
        assert!(
            !has_talent(&world, IRONHIDE),
            "anti-ghost: no dregg-bought talent"
        );

        // Echoes cannot be injected without a real death (meta's grant is death-gated).
        let inject = meta::grant_echoes(&world, 9);
        assert!(
            matches!(inject, Err(WorldError::Refused(_))),
            "granting echoes to a living hero is refused, got {inject:?}"
        );
        assert_eq!(meta::echoes(&world), 0, "anti-ghost: still no echoes");

        // The ONLY path: a real death funds echoes, which buys the talent.
        progression::perish(&world).expect("a real death");
        meta::grant_echoes(&world, 6).expect("the death funds echoes");
        claim_talent(&world, IRONHIDE).expect("death-earned echoes buy the talent");
        assert!(
            has_talent(&world, IRONHIDE),
            "bought with earned echoes, never dregg"
        );
    }
}
