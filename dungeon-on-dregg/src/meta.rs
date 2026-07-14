//! # `meta` — META-PROGRESSION-ON-DEATH: a lost run ADVANCES you.
//!
//! The [`bloodgate`](crate::bloodgate) / [`progression`](crate::progression) pattern makes a
//! hardcore run genuinely LOSABLE: a reckless line strands you into a real committed DEFEAT and the
//! character's `dead` flag is set [`WriteOnce`](dregg_app_framework::StateConstraint::WriteOnce)-final.
//! That is the STAKES. This module is the RETENTION LOOP the flagship strategy (docs Phase 2) names:
//! the Hades / FTL reframe that **democratizes permadeath** — a death is not pure loss, it ADVANCES
//! a persistent meta-progression, so "you erred, AND you progressed."
//!
//! It adds two slots to the persistent character cell (the [`progression`](crate::progression) hero
//! cell — the SAME cell that carries `xp`/`level`/`class`/`dead`), each with a real executor tooth:
//!
//! | slot | field    | tooth (executor-enforced `StateConstraint`)                              |
//! |------|----------|--------------------------------------------------------------------------|
//! | 6    | `echoes` | the META-CURRENCY. Global [`Monotonic`] (only ACCRUES, never spent down); |
//! |      |          | a grant is [`StrictMonotonic`] **and** `FieldEquals(dead, 1)` — granted   |
//! |      |          | ONLY when a run has truly ended in death.                                |
//! | 7    | `boon`   | the persistent UNLOCK. Global [`WriteOnce`]; a claim is                   |
//! |      |          | `FieldGte(echoes, `[`BOON_PRICE`]`)` — bought only with enough accrued    |
//! |      |          | echoes, and set ONCE.                                                     |
//!
//! [`Monotonic`]: dregg_app_framework::StateConstraint::Monotonic
//! [`StrictMonotonic`]: dregg_app_framework::StateConstraint::StrictMonotonic
//! [`WriteOnce`]: dregg_app_framework::StateConstraint::WriteOnce
//!
//! ## The meta-currency is granted ONLY on a real death (deeper = more)
//!
//! [`grant_echoes`] is a real turn under [`GRANT_ECHOES_METHOD`] whose case carries
//! `FieldEquals(dead, 1)` (the character IS dead — a real committed death happened) **and**
//! `StrictMonotonic(echoes)` (a real positive accrual). So:
//!
//! - A grant on a LIVING character (a WON or unfinished run: `dead == 0`) fails `FieldEquals(dead, 1)`
//!   and is a REAL [`WorldError::Refused`](spween_dregg::WorldError) — a won run grants NOTHING.
//! - The amount is [`echoes_for_depth`]`(depth)` — a deeper death grants MORE. The depth is the run's
//!   real committed `depth` (the caller passes it, exactly as the earned-XP amount is run-supplied);
//!   the tooth guarantees the LEDGER invariant (echoes accrue monotonically, ONLY on a real death),
//!   not the game-balance of the curve.
//!
//! ## The unlock is bought with enough echoes, and set ONCE
//!
//! [`claim_boon`] is a real turn under [`CLAIM_BOON_METHOD`] whose case carries
//! `FieldGte(echoes, `[`BOON_PRICE`]`)` (you have ACCRUED enough) + `WriteOnce(boon)` (the unlock is
//! claimed once). A claim WITHOUT enough echoes fails the `FieldGte` and is refused. Because `echoes`
//! is monotone (never spent down), the price is an accrual THRESHOLD — a floor you reach across one
//! deep death or several shallower ones — not a balance you deplete. The claimed `boon` is real cell
//! state that PERSISTS on the character sheet, so a next run STARTS with it.
//!
//! ## Why this does not break the no-cheat leaderboard's fairness
//!
//! The boon is a MODEST, universal starting nudge (a small permanent floor-raiser / an unlocked
//! path), not a power that the board cannot normalize: the daily leaderboard re-executes each run to
//! the WIN against the SAME beacon-seeded world and ranks by turns/depth, and every player earns the
//! same boon on the same terms. A starting nudge raises the floor for everyone; it does not forge a
//! run (the run is still really played + replay-verified) nor grant an edge the ranking cannot see.
//!
//! ## Honest scope
//!
//! - `echoes` / `boon` are REAL committed cell state on the persistent hero cell; the grant + claim
//!   are REAL gated turns; the gates are REAL executor `StateConstraint`s (driven non-vacuously in
//!   [`mod meta_tests`]: a grant on a living character and a claim below the price are real refusals
//!   that commit nothing; a real death then funds a grant that funds a claim).
//! - The depth→echoes amount is run-supplied (the run reports its real committed depth), exactly the
//!   earned-XP model in [`progression::gain_xp`]. Binding the amount to a *replay-verified* depth
//!   (rather than a supplied one) is the same succinct-proof frontier the XP grant names.
//! - What a fuller meta-progression adds (named, not built here): a TREE of unlocks (each a
//!   `FieldGte(echoes, price_k)` + `WriteOnce(boon_k)` slot), cosmetic legacies (a fallen character's
//!   name/glyph carried into the next), and wiring the boon into a run's STARTING resources (a
//!   starting field-dressing / +HP) as a compiler-emitted seed — each additive on this same tooth.

use std::sync::Arc;

use dregg_app_framework::{
    CellProgram, Effect, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    field_from_u64, symbol,
};
use spween_dregg::{CompiledStory, WorldCell, WorldError};

use crate::progression::{self, DEAD_SLOT};

// ── The two meta slots (on the persistent hero cell, beyond xp/level/class/abilities/dead) ──

/// `echoes` — the META-CURRENCY slot. Globally [`Monotonic`](StateConstraint::Monotonic) (it only
/// ACCRUES); a grant is a [`StrictMonotonic`](StateConstraint::StrictMonotonic) + `FieldEquals(dead, 1)`
/// turn — earned ONLY when a run has truly ended in death.
pub const ECHOES_SLOT: u8 = 6;
/// `boon` — the persistent UNLOCK slot. Globally [`WriteOnce`](StateConstraint::WriteOnce); a claim
/// is a `FieldGte(echoes, `[`BOON_PRICE`]`)`-gated turn — the unlock is real, once-set cell state.
pub const BOON_SLOT: u8 = 7;

// ── The meta turn methods (the driver + the program agree on these) ──────────────

/// The method a [`grant_echoes`] turn presents. Its case carries `FieldEquals(dead, 1)` (a real
/// death happened) + `StrictMonotonic(echoes)` (a real positive accrual).
pub const GRANT_ECHOES_METHOD: &str = "meta/grant_echoes";
/// The method a [`claim_boon`] turn presents. Its case carries `FieldGte(echoes, `[`BOON_PRICE`]`)`
/// (enough accrued) + `WriteOnce(boon)` (claimed once).
pub const CLAIM_BOON_METHOD: &str = "meta/claim_boon";

// ── The (modest) meta curve ──────────────────────────────────────────────────────

/// The base echoes a death grants for reaching the trial at all (a shallow death still advances you
/// a little — the democratizing floor).
pub const ECHOES_BASE: u64 = 10;
/// Extra echoes granted per unit of depth reached — "deeper death = more."
pub const ECHOES_PER_DEPTH: u64 = 5;
/// The accrued-echoes THRESHOLD that unlocks the boon (a modest floor — one deep death or a couple
/// of shallow ones). Because `echoes` is monotone this is a threshold to REACH, not a cost to spend.
pub const BOON_PRICE: u64 = 30;
/// The value the `boon` slot lands at on a claim (the unlock marker — a modest permanent nudge a
/// next run starts holding).
pub const BOON_VALUE: u64 = 1;

/// The echoes a death at `depth` grants — the meta-currency accrual, monotone in depth so a deeper
/// death advances you more. Modest by design (a starting nudge, not power-creep).
pub fn echoes_for_depth(depth: u64) -> u64 {
    ECHOES_BASE + ECHOES_PER_DEPTH * depth
}

// ── The meta-augmented hero cell (progression + the two meta teeth) ───────────────

/// **Build the persistent hero cell's [`CompiledStory`] WITH the meta-progression teeth installed.**
/// Starts from [`progression::hero_story`] (xp / level / class / abilities / dead) and adds, on the
/// SAME cell:
///
/// 1. Two global invariants ANDed onto the existing `Always` case: `echoes`
///    [`Monotonic`](StateConstraint::Monotonic) (only accrues) and `boon`
///    [`WriteOnce`](StateConstraint::WriteOnce) (the unlock is set once, never rewritten).
/// 2. A [`GRANT_ECHOES_METHOD`] case: `FieldEquals(dead, 1)` (granted ONLY on a real death) +
///    `StrictMonotonic(echoes)` (a real positive accrual).
/// 3. A [`CLAIM_BOON_METHOD`] case: `FieldGte(echoes, `[`BOON_PRICE`]`)` (bought with enough accrued
///    echoes) + `FieldEquals(boon, `[`BOON_VALUE`]`)` (lands the marker) + `WriteOnce(boon)`.
///
/// The result is a real [`CellProgram::Cases`] the executor enforces move-for-move — additive to and
/// fully compatible with every existing progression turn.
pub fn meta_hero_story() -> CompiledStory {
    let mut story = progression::hero_story();

    // Register the two meta slots so `read_var` / `seed_var` resolve them by name.
    story
        .var_slots
        .insert("echoes".to_string(), ECHOES_SLOT as usize);
    story
        .var_slots
        .insert("boon".to_string(), BOON_SLOT as usize);

    let CellProgram::Cases(cases) = &mut story.program else {
        panic!("the hero story is a Cases program");
    };

    // 1. Extend the global invariants (the single `Always` case) with the meta invariants:
    //    echoes only ever accrues, and the boon is set once.
    let always = cases
        .iter_mut()
        .find(|c| matches!(c.guard, TransitionGuard::Always))
        .expect("hero_story installs a global Always invariant case");
    always
        .constraints
        .push(StateConstraint::Monotonic { index: ECHOES_SLOT });
    always
        .constraints
        .push(StateConstraint::WriteOnce { index: BOON_SLOT });

    // 2. grant_echoes — a real, strictly-positive accrual, ONLY on a dead character (a run that has
    //    truly ended in death). A grant on a living character fails `FieldEquals(dead, 1)`.
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(GRANT_ECHOES_METHOD),
        },
        constraints: vec![
            StateConstraint::FieldEquals {
                index: DEAD_SLOT,
                value: field_from_u64(1),
            },
            StateConstraint::StrictMonotonic { index: ECHOES_SLOT },
        ],
    });

    // 3. claim_boon — the unlock, bought with enough ACCRUED echoes and set once.
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(CLAIM_BOON_METHOD),
        },
        constraints: vec![
            StateConstraint::FieldGte {
                index: ECHOES_SLOT,
                value: field_from_u64(BOON_PRICE),
            },
            StateConstraint::FieldEquals {
                index: BOON_SLOT,
                value: field_from_u64(BOON_VALUE),
            },
            StateConstraint::WriteOnce { index: BOON_SLOT },
        ],
    });

    story
}

/// **Deploy a persistent hero cell WITH meta-progression** as a real world-cell. Deterministic in
/// `seed` (re-deploy reproduces the same identity + hashes). This is the cell
/// [`Character`](../../dreggnet_offerings/character/struct.Character.html) deploys, so a character
/// carries `echoes` / `boon` alongside `xp` / `level` / `class` / `dead`.
pub fn deploy_meta_hero(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(meta_hero_story()), seed)
        .expect("the meta hero cell deploys")
}

// ── The meta turns (each ONE real cap-bounded turn) ───────────────────────────────

/// **Grant the meta-currency for a death at `depth`** — a real turn under [`GRANT_ECHOES_METHOD`]
/// writing `echoes += `[`echoes_for_depth`]`(depth)`. The executor admits it ONLY when the character
/// is dead (`FieldEquals(dead, 1)`) and the accrual is strictly positive
/// ([`StrictMonotonic`](StateConstraint::StrictMonotonic)); a grant on a living character (a won /
/// unfinished run) is a real [`WorldError::Refused`] that commits nothing.
pub fn grant_echoes(world: &WorldCell, depth: u64) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    let new_echoes = world.read_var("echoes") + echoes_for_depth(depth);
    world.apply_raw(
        GRANT_ECHOES_METHOD,
        vec![Effect::SetField {
            cell,
            index: ECHOES_SLOT as usize,
            value: field_from_u64(new_echoes),
        }],
    )
}

/// **Claim the persistent unlock** — a real turn under [`CLAIM_BOON_METHOD`] writing `boon =
/// `[`BOON_VALUE`]. The executor GATES it on `FieldGte(echoes, `[`BOON_PRICE`]`)`: without enough
/// accrued echoes the kernel REFUSES it (a real [`WorldError::Refused`]) and nothing commits. The
/// global `WriteOnce(boon)` makes it a one-time claim.
pub fn claim_boon(world: &WorldCell) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    world.apply_raw(
        CLAIM_BOON_METHOD,
        vec![Effect::SetField {
            cell,
            index: BOON_SLOT as usize,
            value: field_from_u64(BOON_VALUE),
        }],
    )
}

/// Current accrued meta-currency (the committed `echoes` slot).
pub fn echoes(world: &WorldCell) -> u64 {
    world.read_var("echoes")
}

/// Current unlock marker (the committed `boon` slot).
pub fn boon(world: &WorldCell) -> u64 {
    world.read_var("boon")
}

/// Whether the persistent unlock has been claimed (the `boon` slot is set).
pub fn has_boon(world: &WorldCell) -> bool {
    boon(world) != 0
}

#[cfg(test)]
mod meta_tests {
    //! Meta-progression-on-death, each DRIVEN on the real hero `WorldCell`: a real death grants the
    //! meta-currency (a won / unfinished run grants none); a deeper death grants more; the currency
    //! is monotone; enough accrued currency buys the WriteOnce unlock (too little is refused); a
    //! forged grant / claim is refused; and the existing progression turns stay intact.
    use super::*;
    use crate::progression::{self, WARRIOR};
    use dregg_app_framework::Effect;

    /// Every meta rule is a REAL kernel predicate: introspect the installed program and confirm the
    /// grant carries `FieldEquals(dead, 1)` + `StrictMonotonic(echoes)`, the claim carries
    /// `FieldGte(echoes, BOON_PRICE)` + `WriteOnce(boon)`, and the global invariants carry
    /// `Monotonic(echoes)` + `WriteOnce(boon)`.
    #[test]
    fn meta_teeth_are_real_kernel_predicates() {
        let story = meta_hero_story();

        let grant = progression::case_constraints(&story, GRANT_ECHOES_METHOD);
        assert!(
            grant.iter().any(|c| matches!(
                c, StateConstraint::FieldEquals { index, value }
                    if *index == DEAD_SLOT && *value == field_from_u64(1)
            )),
            "grant is gated FieldEquals(dead, 1) — only a real death funds echoes; got {grant:?}"
        );
        assert!(
            grant.iter().any(
                |c| matches!(c, StateConstraint::StrictMonotonic { index } if *index == ECHOES_SLOT)
            ),
            "grant is StrictMonotonic(echoes) — a real positive accrual; got {grant:?}"
        );

        let claim = progression::case_constraints(&story, CLAIM_BOON_METHOD);
        assert!(
            claim.iter().any(|c| matches!(
                c, StateConstraint::FieldGte { index, value }
                    if *index == ECHOES_SLOT && *value == field_from_u64(BOON_PRICE)
            )),
            "claim is gated FieldGte(echoes, {BOON_PRICE}); got {claim:?}"
        );
        assert!(
            claim
                .iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == BOON_SLOT)),
            "claim sets WriteOnce(boon) — the unlock is claimed once; got {claim:?}"
        );

        // The global invariants (the Always case) carry the meta invariants.
        let CellProgram::Cases(cases) = &story.program else {
            panic!("Cases program");
        };
        let always = cases
            .iter()
            .find(|c| matches!(c.guard, TransitionGuard::Always))
            .expect("Always case");
        assert!(
            always.constraints.iter().any(
                |c| matches!(c, StateConstraint::Monotonic { index } if *index == ECHOES_SLOT)
            ),
            "echoes is globally Monotonic (only accrues); got {:?}",
            always.constraints
        );
        assert!(
            always
                .constraints
                .iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == BOON_SLOT)),
            "boon is globally WriteOnce; got {:?}",
            always.constraints
        );
    }

    /// THE HARD GATE (non-vacuous): echoes are granted ONLY on a real death. On a LIVING character
    /// (a won / unfinished run) the grant is a REAL refusal that commits nothing; after a real
    /// committed death (`perish`) the SAME grant commits — the only difference is the death.
    #[test]
    fn echoes_granted_only_on_a_real_death() {
        let world = deploy_meta_hero(30);
        progression::choose_class(&world, WARRIOR).expect("class");
        assert!(!progression::is_dead(&world), "alive so far");
        assert_eq!(echoes(&world), 0, "fresh: no echoes");

        // A LIVING character's run (won or unfinished) grants NOTHING — FieldEquals(dead, 1) fails.
        let refused = grant_echoes(&world, 5);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a living character earns no echoes (a won/unfinished run grants none), got {refused:?}"
        );
        assert_eq!(echoes(&world), 0, "anti-ghost: no echoes without a death");

        // A real committed death, then the SAME grant commits.
        progression::perish(&world).expect("the death commits");
        assert!(progression::is_dead(&world), "the character is dead");
        grant_echoes(&world, 5).expect("a real death funds the echoes grant");
        assert_eq!(
            echoes(&world),
            echoes_for_depth(5),
            "a death at depth 5 grants echoes_for_depth(5)"
        );
    }

    /// DEEPER DEATH = MORE (non-vacuous). Two characters perish; the one who died DEEPER banks
    /// strictly more echoes.
    #[test]
    fn a_deeper_death_grants_more_echoes() {
        let shallow = deploy_meta_hero(31);
        progression::perish(&shallow).expect("shallow death");
        grant_echoes(&shallow, 2).expect("grant at depth 2");

        let deep = deploy_meta_hero(32);
        progression::perish(&deep).expect("deep death");
        grant_echoes(&deep, 6).expect("grant at depth 6");

        assert!(
            echoes(&deep) > echoes(&shallow),
            "a deeper death (depth 6 → {}) grants MORE than a shallow one (depth 2 → {})",
            echoes(&deep),
            echoes(&shallow)
        );
    }

    /// The meta-currency is MONOTONE — it only accrues. Two deaths' worth of grants stack (a fresh
    /// character seeded with carried echoes accrues on top), and a direct write DOWN is refused by
    /// the global `Monotonic(echoes)`.
    #[test]
    fn echoes_are_monotonic_only_accrue() {
        let world = deploy_meta_hero(33);
        progression::perish(&world).expect("death");
        grant_echoes(&world, 3).expect("first accrual");
        let after_first = echoes(&world);
        grant_echoes(&world, 4).expect("second accrual stacks");
        assert!(
            echoes(&world) > after_first,
            "echoes accrue (strictly up on each grant)"
        );

        // A direct attempt to WRITE echoes DOWN is refused by global Monotonic(echoes).
        let cell = world.cell_id();
        let down = world.apply_raw(
            GRANT_ECHOES_METHOD,
            vec![Effect::SetField {
                cell,
                index: ECHOES_SLOT as usize,
                value: field_from_u64(1),
            }],
        );
        assert!(
            matches!(down, Err(WorldError::Refused(_))),
            "writing echoes down is refused (Monotonic), got {down:?}"
        );
        assert!(
            echoes(&world) > after_first,
            "anti-ghost: echoes not lowered"
        );
    }

    /// THE UNLOCK (both directions, non-vacuous): enough ACCRUED echoes buys the boon; too little is
    /// refused by `FieldGte(echoes, BOON_PRICE)`; and a claimed boon is `WriteOnce`.
    #[test]
    fn the_boon_is_bought_with_enough_echoes_and_is_writeonce() {
        // TOO LITTLE: a shallow death banks below the price → the claim is refused.
        let poor = deploy_meta_hero(34);
        progression::perish(&poor).expect("death");
        grant_echoes(&poor, 1).expect("a shallow grant"); // 10 + 5 = 15 < 30
        assert!(echoes(&poor) < BOON_PRICE, "below the boon price");
        let refused = claim_boon(&poor);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a claim below the price is refused (FieldGte), got {refused:?}"
        );
        assert_eq!(boon(&poor), 0, "anti-ghost: no boon without enough echoes");

        // ENOUGH: a deep death banks over the price → the claim commits.
        let rich = deploy_meta_hero(35);
        progression::perish(&rich).expect("death");
        grant_echoes(&rich, 6).expect("a deep grant"); // 10 + 30 = 40 >= 30
        assert!(echoes(&rich) >= BOON_PRICE, "at/over the boon price");
        assert!(!has_boon(&rich), "no boon yet");
        claim_boon(&rich).expect("enough echoes buys the boon");
        assert!(has_boon(&rich), "the boon is claimed");
        assert_eq!(boon(&rich), BOON_VALUE, "the unlock marker landed");

        // WriteOnce-final: a rewrite of the claimed boon to a DIFFERENT value is refused (the global
        // `WriteOnce(boon)` bars the 1→2 change) — the unlock cannot be re-keyed once set.
        let cell = rich.cell_id();
        let rewrite = rich.apply_raw(
            CLAIM_BOON_METHOD,
            vec![Effect::SetField {
                cell,
                index: BOON_SLOT as usize,
                value: field_from_u64(2),
            }],
        );
        assert!(
            matches!(rewrite, Err(WorldError::Refused(_))),
            "rewriting the claimed boon to a different value is refused (WriteOnce), got {rewrite:?}"
        );
        assert_eq!(boon(&rich), BOON_VALUE, "anti-ghost: the boon is unchanged");
        // An idempotent re-claim (the same value) is a harmless no-op — you already hold it.
        claim_boon(&rich).expect("an idempotent re-claim (1→1) is a no-op");
        assert_eq!(boon(&rich), BOON_VALUE);
    }

    /// THE FORGED-META TOOTH (non-vacuous): a meta-currency grant under a NON-sanctioned method is a
    /// real executor refusal (default-deny); a boon claim without the accrued echoes is refused; and
    /// a grant on a LIVING character is refused. The teeth bite a forgery from every angle.
    #[test]
    fn a_forged_meta_grant_is_refused() {
        let world = deploy_meta_hero(36);
        let cell = world.cell_id();

        // Forge echoes under an unknown method → default-deny refusal.
        let forged = world.apply_raw(
            "cheat/inject_echoes",
            vec![Effect::SetField {
                cell,
                index: ECHOES_SLOT as usize,
                value: field_from_u64(9_999),
            }],
        );
        assert!(
            matches!(forged, Err(WorldError::Refused(_))),
            "a forged echoes grant (unknown method) is refused, got {forged:?}"
        );
        assert_eq!(echoes(&world), 0, "anti-ghost: no forged echoes");

        // Claim the boon with zero accrued echoes → FieldGte refuses (unlock-without-currency).
        let no_currency = claim_boon(&world);
        assert!(
            matches!(no_currency, Err(WorldError::Refused(_))),
            "a boon claim without the accrued echoes is refused, got {no_currency:?}"
        );
        assert_eq!(boon(&world), 0, "anti-ghost: no forged unlock");

        // Grant on a LIVING character (no death) → FieldEquals(dead, 1) refuses.
        let alive_grant = grant_echoes(&world, 9);
        assert!(
            matches!(alive_grant, Err(WorldError::Refused(_))),
            "an echoes grant without a real death is refused, got {alive_grant:?}"
        );
        assert_eq!(echoes(&world), 0, "anti-ghost: still no echoes");
    }

    /// The existing progression turns stay intact on the meta-augmented cell: choose class, earn XP,
    /// reach level 1, perish — every one still commits, so meta is purely additive.
    #[test]
    fn existing_progression_turns_stay_intact() {
        let world = deploy_meta_hero(37);
        progression::choose_class(&world, WARRIOR).expect("class still commits");
        progression::level_up(&world).expect("free level 1 still commits");
        progression::gain_xp(&world, 50).expect("xp gain still commits");
        assert_eq!(world.read_var("xp"), 50);
        progression::perish(&world).expect("death still commits");
        assert!(progression::is_dead(&world));
    }
}
