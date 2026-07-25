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
//! ## The TOMB path — the accrual a run's own record pays for
//!
//! [`grant_echoes`] takes the depth as an ARGUMENT, and nothing in the kernel prices that number
//! (the doc-comment below used to call this "run-supplied, exactly the earned-XP model"; in
//! practice callers across the tree pass `6`, `7`, `12` to a dungeon that has FOUR floors, because
//! whatever number you type is the number you get). That is a ratchet a player mints for
//! themselves. [`grant_echoes_at_depth`] is the replacement: one method PER REACHABLE DEPTH, each
//! carrying an EXACT [`FieldDelta`](StateConstraint::FieldDelta) for that depth's payout, so
//!
//! * the set of payable depths is a CLOSED SET OF METHODS in the deployed program — a "death at
//!   depth 12" has no case and is a default-deny refusal, not a bigger payout;
//! * the amount is pinned by the kernel, not by the caller (`FieldDelta{echoes, e(d)}`);
//! * the redemption also advances [`TOMBS_SLOT`] by exactly one, so `tombs` is a truthful count of
//!   redeemed death-records rather than a number the app keeps.
//!
//! [`crate::tomb`] is the only thing that should call it: its [`Tomb`](crate::tomb::Tomb) reads the
//! depth off the run's COMMITTED cell state and cannot be constructed any other way.
//!
//! ## The SLOT-BOUND currency tooth (a hole that was live until this commit)
//!
//! The `FieldEquals(dead, 1)` "only a real death pays" gate lived ONLY on the
//! [`GRANT_ECHOES_METHOD`] case. But `apply_raw` is public and the evaluator runs EVERY matching
//! case, so `SetField(echoes, 9_999)` STAPLED onto a legitimate `hero/gain_xp` turn — on a LIVING
//! character — met only the global `Monotonic(echoes)` and committed. The meta-currency was
//! mintable without dying at all, which is exactly the hole the `boon` and talent-tree
//! `SlotChanged` cases were added to close one level further up (`meta.rs` case 3,
//! `dreggnet_gear::talents`), left open on the currency those prices are denominated in.
//! [`meta_hero_story`] now carries a `SlotChanged { ECHOES_SLOT }` case with `FieldEquals(dead, 1)`:
//! the death gate binds to the WRITE, whoever authored it. Driven:
//! [`meta_tests::a_stapled_echoes_write_cannot_mint_currency_on_a_living_sheet`].
//!
//! ## The RETURN RIGHT — the ratchet that is not power
//!
//! [`TOMB_DAYS_SLOT`] is a bitmask over the [`DAYS`] daily maps: bit `k` is set when day `k`'s map
//! has killed you. It is globally [`Monotonic`](StateConstraint::Monotonic), each bit is set by its
//! own method under an EXACT `FieldDelta{tomb_days, 1 << k}` (so a mark lands one specific day and
//! a re-mark of a day you already hold is a refusal, not a silent no-op), and every mark is gated
//! `FieldEquals(dead, 1)`.
//!
//! What it buys is deliberately NOT power: it is the right to open a later descent on a map that
//! has already killed you ([`crate::tomb::may_return_to`]) instead of taking the beacon's draw.
//! Every one of the 16 maps is Lean-checked completable in 20–26 of the 26 breath
//! (`Dungeon.costAt_tense`), so none of them is *easier* — going back is a choice of battlefield,
//! not a discount, and the only way to earn a battlefield is to lose on it.
//!
//! ## Honest scope
//!
//! - `echoes` / `boon` / `tomb_days` / `tombs` are REAL committed cell state on the persistent hero
//!   cell; the grant + claim + mark are REAL gated turns; the gates are REAL executor
//!   `StateConstraint`s (driven non-vacuously in [`mod meta_tests`]).
//! - The kernel prices the SHAPE of the accrual (only on a dead sheet, only at a depth the dungeon
//!   actually has, only in that depth's exact quantum, one tomb counted per grant). It does NOT
//!   price the accrual against A SPECIFIC RUN ON ANOTHER CELL: the hero program cannot name a
//!   per-run descent cell, so nothing in the executor stops a second grant funded by a second real
//!   dead run. Binding the two cells needs the run's terminal state carried into the redemption
//!   turn as a witness the executor verifies (a `BoundDelta` / `ObservedFieldEquals` shape against
//!   the descent cell's finalized roots) — named, not built, and spelled out in [`crate::tomb`].
//! - [`grant_echoes`] (the by-argument legacy path) is KEPT because four other crates drive it, and
//!   it is now dead-gated at the write like everything else — but its AMOUNT is still un-priced.
//!   Retiring it is a cross-crate cutover this module cannot make alone.

use std::sync::Arc;

use dregg_app_framework::{
    CellProgram, Effect, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    field_from_u64, symbol,
};
use spween_dregg::{CompiledStory, WorldCell, WorldError};

use crate::descent::{DAYS, FLOORS};
use crate::progression::{self, DEAD_SLOT};

// ── The two meta slots (on the persistent hero cell, beyond xp/level/class/abilities/dead) ──

/// `echoes` — the META-CURRENCY slot. Globally [`Monotonic`](StateConstraint::Monotonic) (it only
/// ACCRUES); a grant is a [`StrictMonotonic`](StateConstraint::StrictMonotonic) + `FieldEquals(dead, 1)`
/// turn — earned ONLY when a run has truly ended in death.
pub const ECHOES_SLOT: u8 = 6;
/// `boon` — the persistent UNLOCK slot. Globally [`WriteOnce`](StateConstraint::WriteOnce); a claim
/// is a `FieldGte(echoes, `[`BOON_PRICE`]`)`-gated turn — the unlock is real, once-set cell state.
pub const BOON_SLOT: u8 = 7;
/// `tomb_days` — the RETURN-RIGHT mask over the [`DAYS`] daily maps: bit `k` set ⟺ day `k`'s map
/// has killed you. Globally [`Monotonic`](StateConstraint::Monotonic); each bit is set by its own
/// [`mark_tomb_day_method`] under an exact `FieldDelta{tomb_days, 1 << k}`, gated on a real death.
///
/// Slots 8–12 belong to [`dreggnet_gear::talents`](../../dreggnet_gear/talents/index.html) (the
/// four talent slots plus the respec generation), which builds its story on top of this one; the
/// meta slots resume at 13 so the two never collide on the same cell.
pub const TOMB_DAYS_SLOT: u8 = 13;
/// `tombs` — a truthful count of REDEEMED death-records. Globally
/// [`Monotonic`](StateConstraint::Monotonic); every [`grant_echoes_at_depth`] turn must advance it
/// by exactly one (`FieldDelta{tombs, 1}`) and no turn may move it by anything else, so it counts
/// tomb redemptions rather than tracking them in app memory.
pub const TOMBS_SLOT: u8 = 14;

// ── The meta turn methods (the driver + the program agree on these) ──────────────

/// The method a [`grant_echoes`] turn presents. Its case carries `FieldEquals(dead, 1)` (a real
/// death happened) + `StrictMonotonic(echoes)` (a real positive accrual).
///
/// ⚠ LEGACY: the AMOUNT this method writes is whatever the caller computed — the kernel only
/// checks it went up. [`grant_echoes_at_depth`] is the priced replacement.
pub const GRANT_ECHOES_METHOD: &str = "meta/grant_echoes";
/// The method a [`claim_boon`] turn presents. Its case carries `FieldGte(echoes, `[`BOON_PRICE`]`)`
/// (enough accrued) + `WriteOnce(boon)` (claimed once).
pub const CLAIM_BOON_METHOD: &str = "meta/claim_boon";

/// The method a [`grant_echoes_at_depth`] turn presents, one per depth the dungeon actually has
/// (`0..=`[`FLOORS`]). The case carries `FieldEquals(dead, 1)` + an EXACT
/// `FieldDelta{echoes, `[`echoes_for_depth`]`(depth)}` + `FieldDelta{tombs, 1}`. A depth outside
/// the dungeon names no case at all and is a default-deny refusal.
pub fn tomb_grant_method(depth: u64) -> String {
    format!("meta/grant_echoes/tomb/{depth}")
}

/// The method a [`mark_tomb_day`] turn presents, one per daily map (`0..`[`DAYS`]). The case
/// carries `FieldEquals(dead, 1)` + an EXACT `FieldDelta{tomb_days, 1 << day}`.
pub fn mark_tomb_day_method(day: usize) -> String {
    format!("meta/mark_tomb_day/{day}")
}

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
        .insert("echoes".to_string(), ECHOES_SLOT as u64);
    story.var_slots.insert("boon".to_string(), BOON_SLOT as u64);
    story
        .var_slots
        .insert("tomb_days".to_string(), TOMB_DAYS_SLOT as u64);
    story
        .var_slots
        .insert("tombs".to_string(), TOMBS_SLOT as u64);

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
    // The tomb ledger only ever grows: a day whose map has killed you stays killed, and a
    // redeemed death-record is never un-counted.
    always.constraints.push(StateConstraint::Monotonic {
        index: TOMB_DAYS_SLOT,
    });
    always
        .constraints
        .push(StateConstraint::Monotonic { index: TOMBS_SLOT });

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

    // 3. THE SLOT-BOUND GATE — the tooth that makes the boon PRICE real.
    //
    // A `MethodIs` case gates only turns that PRESENT the claim method. But `apply_raw` is public:
    // a client can staple `SetField(boon, 1)` onto ANY other method's turn (e.g. a legitimate
    // `meta/grant_echoes`), where no `meta/claim_boon` case matches and the global `Always`
    // `WriteOnce(boon)` happily permits the FIRST write (`cell/src/program/eval.rs:379-383`,
    // `old_zero`) — so the boon lands with NO price check. (Driven:
    // `a_stapled_boon_write_cannot_ride_another_methods_turn`, which committed the unlock at
    // 15/30 echoes before this case existed.)
    //
    // `SlotChanged` binds the price to the WRITE rather than the method: the case fires on ANY
    // transition that moves the `boon` slot, whoever authored it. The evaluator runs EVERY matching
    // case (`eval.rs:104-120`), so this gate composes with the authoring method's own constraints
    // instead of being skipped by it. `SlotChanged` is NOT method-dispatching
    // (`TransitionGuard::is_method_dispatching`), so default-deny is unaffected.
    cases.push(TransitionCase {
        guard: TransitionGuard::SlotChanged { index: BOON_SLOT },
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

    // 4. claim_boon — the method a legitimate claim dispatches under. `SlotChanged` is NOT
    //    method-dispatching, so without this case `meta/claim_boon` would be an unknown symbol and
    //    default-deny. It carries the same gates (defence in depth; the SlotChanged case above is
    //    the load-bearing one).
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

    // 5. THE SLOT-BOUND CURRENCY GATE — the tooth that makes "only a real death pays" real.
    //
    // "Granted ONLY on a real death" lived on the `MethodIs{GRANT_ECHOES_METHOD}` case (case 2).
    // A `MethodIs` case gates only turns that PRESENT that method, and `apply_raw` is public — so
    // `SetField(echoes, 9_999)` STAPLED onto a legitimate `hero/gain_xp` turn matched no grant
    // case, faced only the global `Monotonic{echoes}` (0 -> 9_999 is monotone), and COMMITTED, on
    // a LIVING character. The meta-currency every price in the tree is denominated in was mintable
    // without dying. (Driven: `a_stapled_echoes_write_cannot_mint_currency_on_a_living_sheet`,
    // which committed 9_999 echoes on a living hero before this case existed.)
    //
    // `SlotChanged` binds the death gate to THE WRITE rather than to the method: the case fires on
    // any transition that moves `echoes`, whoever authored it. The evaluator runs EVERY matching
    // case (`cell/src/program/eval.rs:104-120`), so this composes with the authoring method's own
    // constraints instead of being skipped by it, and `SlotChanged` is not method-dispatching so
    // default-deny is unaffected.
    cases.push(TransitionCase {
        guard: TransitionGuard::SlotChanged { index: ECHOES_SLOT },
        constraints: vec![StateConstraint::FieldEquals {
            index: DEAD_SLOT,
            value: field_from_u64(1),
        }],
    });

    // 6. THE PRICED TOMB GRANTS — one method per depth the dungeon actually has, each pinning the
    //    payout with an EXACT `FieldDelta`. This is what stops the amount being whatever the
    //    caller typed: a redemption for a death at depth `d` can move `echoes` by
    //    `echoes_for_depth(d)` and by nothing else, and it must count the tomb.
    for depth in 0..=FLOORS {
        cases.push(TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(&tomb_grant_method(depth)),
            },
            constraints: vec![
                StateConstraint::FieldEquals {
                    index: DEAD_SLOT,
                    value: field_from_u64(1),
                },
                StateConstraint::FieldDelta {
                    index: ECHOES_SLOT,
                    delta: field_from_u64(echoes_for_depth(depth)),
                },
                StateConstraint::FieldDelta {
                    index: TOMBS_SLOT,
                    delta: field_from_u64(1),
                },
            ],
        });
    }

    // 7. The tomb COUNT is slot-bound too: whatever method moves it, it moves by exactly one, on a
    //    dead sheet. So `tombs` cannot be inflated to fake a long history of deaths.
    cases.push(TransitionCase {
        guard: TransitionGuard::SlotChanged { index: TOMBS_SLOT },
        constraints: vec![
            StateConstraint::FieldEquals {
                index: DEAD_SLOT,
                value: field_from_u64(1),
            },
            StateConstraint::FieldDelta {
                index: TOMBS_SLOT,
                delta: field_from_u64(1),
            },
        ],
    });

    // 8. THE RETURN RIGHT — one method per daily map, each setting exactly that map's bit.
    //    `FieldDelta{tomb_days, 1 << day}` is exact, so marking a day you ALREADY hold is a
    //    refusal (delta 0), not a silent no-op: the caller must check `may_return_to` first.
    for day in 0..DAYS {
        cases.push(TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(&mark_tomb_day_method(day)),
            },
            constraints: vec![
                StateConstraint::FieldEquals {
                    index: DEAD_SLOT,
                    value: field_from_u64(1),
                },
                StateConstraint::FieldDelta {
                    index: TOMB_DAYS_SLOT,
                    delta: field_from_u64(1u64 << day),
                },
            ],
        });
    }

    // 9. And the mask is slot-bound: any write to it must be on a dead sheet, must not clear a day
    //    already earned (`Monotonic`), and cannot exceed one map's worth of bits in magnitude.
    //
    //    RESIDUAL, stated rather than hidden: `FieldDeltaInRange` bounds the delta, it does not pin
    //    it to the set `{1, 2, 4, …, 1 << (DAYS-1)}`. A stapled write can therefore set SEVERAL
    //    day-bits in one turn (any delta in `[1, 1 << (DAYS-1)]`). Pinning it exactly needs a
    //    `SimpleStateConstraint::FieldDelta` variant so the legal quanta can be `AnyOf`-ed; the
    //    cell algebra exposes `FieldDelta` only at the outer `StateConstraint` level, which cannot
    //    be disjoined. That one-variant gap is the reason every price tooth in this crate can bound
    //    a stapled amount but not fix it.
    cases.push(TransitionCase {
        guard: TransitionGuard::SlotChanged {
            index: TOMB_DAYS_SLOT,
        },
        constraints: vec![
            StateConstraint::FieldEquals {
                index: DEAD_SLOT,
                value: field_from_u64(1),
            },
            StateConstraint::Monotonic {
                index: TOMB_DAYS_SLOT,
            },
            StateConstraint::FieldDeltaInRange {
                index: TOMB_DAYS_SLOT,
                min_delta: field_from_u64(1),
                max_delta: field_from_u64(1u64 << (DAYS - 1)),
            },
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
            index: ECHOES_SLOT as u64,
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
            index: BOON_SLOT as u64,
            value: field_from_u64(BOON_VALUE),
        }],
    )
}

/// **Redeem a death at `depth` — the PRICED accrual.** A real turn under
/// [`tomb_grant_method`]`(depth)` writing `echoes += `[`echoes_for_depth`]`(depth)` and
/// `tombs += 1`. Unlike [`grant_echoes`], the amount is not the caller's to choose: the case
/// carries an exact `FieldDelta` for THIS depth, so a payload that writes anything else is refused,
/// and a `depth` the dungeon does not have (`> `[`FLOORS`]) names no case at all and is a
/// default-deny refusal.
///
/// [`crate::tomb::inter`] is the intended caller — it reads `depth` off a run's committed cell
/// state rather than accepting a number.
pub fn grant_echoes_at_depth(world: &WorldCell, depth: u64) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    let new_echoes = world.read_var("echoes") + echoes_for_depth(depth);
    let new_tombs = world.read_var("tombs") + 1;
    world.apply_raw(
        &tomb_grant_method(depth),
        vec![
            Effect::SetField {
                cell,
                index: ECHOES_SLOT as u64,
                value: field_from_u64(new_echoes),
            },
            Effect::SetField {
                cell,
                index: TOMBS_SLOT as u64,
                value: field_from_u64(new_tombs),
            },
        ],
    )
}

/// **Mark a daily map as one that has killed you** — a real turn under
/// [`mark_tomb_day_method`]`(day)` setting bit `day` of [`TOMB_DAYS_SLOT`]. Gated
/// `FieldEquals(dead, 1)` and pinned to that one bit by an exact `FieldDelta`, so a day you already
/// hold is a REFUSAL (delta 0), not a no-op — check [`may_return_to`] first.
pub fn mark_tomb_day(world: &WorldCell, day: usize) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    let next = world.read_var("tomb_days") | (1u64 << (day % DAYS));
    world.apply_raw(
        &mark_tomb_day_method(day % DAYS),
        vec![Effect::SetField {
            cell,
            index: TOMB_DAYS_SLOT as u64,
            value: field_from_u64(next),
        }],
    )
}

/// Current accrued meta-currency (the committed `echoes` slot).
pub fn echoes(world: &WorldCell) -> u64 {
    world.read_var("echoes")
}

/// The committed RETURN-RIGHT mask — bit `k` set ⟺ day `k`'s map has killed this identity.
pub fn tomb_days(world: &WorldCell) -> u64 {
    world.read_var("tomb_days")
}

/// The committed count of redeemed death-records.
pub fn tombs(world: &WorldCell) -> u64 {
    world.read_var("tombs")
}

/// Whether this identity has earned the right to open a later descent on day `day`'s map — i.e.
/// whether that map has killed it. Not a power: every drawn map is Lean-checked completable, so a
/// return is a choice of battlefield, and losing there is the only way to earn one.
pub fn may_return_to(world: &WorldCell, day: usize) -> bool {
    tomb_days(world) & (1u64 << (day % DAYS)) != 0
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
                index: ECHOES_SLOT as u64,
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
                index: BOON_SLOT as u64,
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
                index: ECHOES_SLOT as u64,
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

    /// THE SLOT-BOUND TOOTH (the falsifier for a real, once-live hole): a `boon` write STAPLED onto
    /// a DIFFERENT method's legitimate turn is REFUSED.
    ///
    /// `apply_raw` is public, so a client can append `SetField(boon, 1)` to any turn it is otherwise
    /// entitled to make. Before the [`BOON_SLOT`] `SlotChanged` case existed, the price lived ONLY on
    /// the [`CLAIM_BOON_METHOD`] case, while the global `Always` case's `WriteOnce(boon)` PERMITTED
    /// the FIRST write (`cell/src/program/eval.rs:379-383`, `old_zero`) — and the evaluator runs
    /// EVERY matching case (`eval.rs:104-120`), never "only the matching one". So a boon stapled onto
    /// a legitimate `meta/grant_echoes` met the invariant and faced NO price gate: DRIVEN, it
    /// committed with 15 echoes against a `BOON_PRICE` of 30 — **the unlock at HALF price**.
    ///
    /// The `SlotChanged { index: BOON_SLOT }` case binds the price to THE WRITE rather than to the
    /// method, so it now fires whoever authored the transition.
    #[test]
    fn a_stapled_boon_write_cannot_ride_another_methods_turn() {
        let world = deploy_meta_hero(38);
        progression::choose_class(&world, WARRIOR).expect("class");
        progression::perish(&world).expect("a real death");
        let cell = world.cell_id();

        // A legitimate grant_echoes payload: dead == 1, echoes 0 -> 15 (a real strict accrual).
        let echoes_amount = echoes_for_depth(1);
        assert!(
            echoes_amount < BOON_PRICE,
            "the falsifier is only meaningful when the hero CANNOT afford the boon: \
             {echoes_amount} echoes vs a price of {BOON_PRICE}"
        );

        let stapled = world.apply_raw(
            GRANT_ECHOES_METHOD,
            vec![
                // The echoes write — entirely legitimate on its own.
                Effect::SetField {
                    cell,
                    index: ECHOES_SLOT as u64,
                    value: field_from_u64(echoes_amount),
                },
                // The stapled-on free unlock.
                Effect::SetField {
                    cell,
                    index: BOON_SLOT as u64,
                    value: field_from_u64(BOON_VALUE),
                },
            ],
        );

        assert!(
            matches!(stapled, Err(WorldError::Refused(_))),
            "a boon write stapled onto a grant_echoes turn must be REFUSED — otherwise the unlock \
             is bought at {echoes_amount}/{BOON_PRICE} echoes; got {stapled:?}"
        );
        assert!(
            !has_boon(&world),
            "anti-ghost: no free unlock rode in on another method's turn"
        );
        assert_eq!(
            echoes(&world),
            0,
            "anti-ghost: the refusal committed NOTHING — not even the legitimate echoes half"
        );

        // The AUTHORING method is not the pivot: the same staple under a progression method (itself
        // perfectly legitimate on this cell) is refused too.
        let via_xp = world.apply_raw(
            progression::GAIN_XP_METHOD,
            vec![Effect::SetField {
                cell,
                index: BOON_SLOT as u64,
                value: field_from_u64(BOON_VALUE),
            }],
        );
        assert!(
            matches!(via_xp, Err(WorldError::Refused(_))),
            "a boon staple under a progression method is refused too, got {via_xp:?}"
        );
        assert!(!has_boon(&world), "anti-ghost: still no free unlock");

        // THE GATE IS A PRICE, NOT A BAN: once the echoes are truly accrued, the claim commits.
        grant_echoes(&world, 6).expect("a real deep death funds the echoes");
        assert!(
            echoes(&world) >= BOON_PRICE,
            "the hero can now afford the boon"
        );
        claim_boon(&world).expect("a legitimately-funded claim still commits");
        assert!(has_boon(&world), "the real unlock landed");
    }

    /// THE SLOT-BOUND CURRENCY TOOTH (the falsifier for a hole that was live in HEAD until this
    /// commit): an `echoes` write STAPLED onto a DIFFERENT method's legitimate turn, on a LIVING
    /// character, is REFUSED.
    ///
    /// `apply_raw` is public, so a client can append `SetField(echoes, 9_999)` to any turn it is
    /// otherwise entitled to make. The "granted ONLY on a real death" gate lived on the
    /// `MethodIs{GRANT_ECHOES_METHOD}` case, which such a turn never matches; the only
    /// non-dispatching guard on `echoes` was the global `Always Monotonic{echoes}`, and 0 -> 9_999
    /// is perfectly monotone. DRIVEN, a `SetField(echoes, 9_999)` stapled onto a legitimate
    /// `hero/gain_xp` committed **9,999 echoes on a character that never died** — enough to buy
    /// every boon and every talent in `dreggnet_gear`, whose prices are denominated in this exact
    /// slot. The `SlotChanged{echoes}` case binds the death gate to THE WRITE.
    #[test]
    fn a_stapled_echoes_write_cannot_mint_currency_on_a_living_sheet() {
        let world = deploy_meta_hero(42);
        progression::choose_class(&world, WARRIOR).expect("class");
        assert!(!progression::is_dead(&world), "the hero is ALIVE");
        let cell = world.cell_id();

        // A legitimate gain_xp payload (xp 0 -> 1, strictly monotone, alive) plus a stapled mint.
        let stapled = world.apply_raw(
            progression::GAIN_XP_METHOD,
            vec![
                Effect::SetField {
                    cell,
                    index: progression::XP_SLOT as u64,
                    value: field_from_u64(1),
                },
                Effect::SetField {
                    cell,
                    index: ECHOES_SLOT as u64,
                    value: field_from_u64(9_999),
                },
            ],
        );
        assert!(
            matches!(stapled, Err(WorldError::Refused(_))),
            "an echoes mint stapled onto a gain_xp turn on a LIVING hero must be REFUSED — \
             otherwise every boon/talent price in the tree is free; got {stapled:?}"
        );
        assert_eq!(echoes(&world), 0, "anti-ghost: no minted currency");
        assert_eq!(
            world.read_var("xp"),
            0,
            "anti-ghost: the refusal committed NOTHING, not even the legitimate XP half"
        );

        // The claim_boon method is not the pivot either — the gate binds the WRITE.
        let via_boon = world.apply_raw(
            CLAIM_BOON_METHOD,
            vec![Effect::SetField {
                cell,
                index: ECHOES_SLOT as u64,
                value: field_from_u64(BOON_PRICE),
            }],
        );
        assert!(
            matches!(via_boon, Err(WorldError::Refused(_))),
            "an echoes write under claim_boon on a living hero is refused too, got {via_boon:?}"
        );
        assert_eq!(echoes(&world), 0, "anti-ghost: still no currency");

        // THE GATE IS A DEATH, NOT A BAN: once the hero has really died, the accrual commits.
        progression::perish(&world).expect("a real death");
        grant_echoes_at_depth(&world, 4).expect("a real death funds a real, priced accrual");
        assert_eq!(echoes(&world), echoes_for_depth(4));
    }

    /// THE PRICED ACCRUAL (non-vacuous): the tomb grant's amount is fixed by the KERNEL, not by the
    /// caller. The same method with a forged (larger) payload is refused; a depth the dungeon does
    /// not have names no case and is a default-deny refusal; and the sanctioned call commits
    /// exactly one depth's payout while counting exactly one tomb.
    #[test]
    fn the_tomb_grant_is_priced_by_the_kernel_not_the_caller() {
        let world = deploy_meta_hero(43);
        progression::perish(&world).expect("a real death");
        let cell = world.cell_id();

        // FORGE THE AMOUNT: present the depth-1 method but write the depth-4 payout.
        let forged = world.apply_raw(
            &tomb_grant_method(1),
            vec![
                Effect::SetField {
                    cell,
                    index: ECHOES_SLOT as u64,
                    value: field_from_u64(echoes_for_depth(4)),
                },
                Effect::SetField {
                    cell,
                    index: TOMBS_SLOT as u64,
                    value: field_from_u64(1),
                },
            ],
        );
        assert!(
            matches!(forged, Err(WorldError::Refused(_))),
            "a depth-1 redemption paying the depth-4 amount is refused (FieldDelta), got {forged:?}"
        );
        assert_eq!(echoes(&world), 0, "anti-ghost: nothing minted");

        // A DEPTH THE DUNGEON DOES NOT HAVE: the callers scattered across the tree pass 6, 7, 12
        // to a four-floor dungeon. There is no such case, so there is no such payout.
        let too_deep = grant_echoes_at_depth(&world, FLOORS + 1);
        assert!(
            matches!(too_deep, Err(WorldError::Refused(_))),
            "a death 'at depth {}' in a {FLOORS}-floor dungeon has no method and is default-denied, \
             got {too_deep:?}",
            FLOORS + 1
        );
        assert_eq!(echoes(&world), 0, "anti-ghost: still nothing");

        // THE SANCTIONED PATH: exactly this depth's quantum, exactly one tomb.
        grant_echoes_at_depth(&world, 3).expect("a depth-3 redemption commits");
        assert_eq!(echoes(&world), echoes_for_depth(3));
        assert_eq!(tombs(&world), 1, "one death redeemed, one tomb counted");
        grant_echoes_at_depth(&world, 4).expect("a second, deeper death redeems too");
        assert_eq!(echoes(&world), echoes_for_depth(3) + echoes_for_depth(4));
        assert_eq!(tombs(&world), 2);

        // The COUNT is slot-bound: a stapled jump in `tombs` (faking a long history of deaths, which
        // any future ranking over "runs survived" would read) is refused.
        let inflate = world.apply_raw(
            GRANT_ECHOES_METHOD,
            vec![
                Effect::SetField {
                    cell,
                    index: ECHOES_SLOT as u64,
                    value: field_from_u64(echoes(&world) + 1),
                },
                Effect::SetField {
                    cell,
                    index: TOMBS_SLOT as u64,
                    value: field_from_u64(99),
                },
            ],
        );
        assert!(
            matches!(inflate, Err(WorldError::Refused(_))),
            "inflating the tomb count is refused (FieldDelta +1), got {inflate:?}"
        );
        assert_eq!(tombs(&world), 2, "anti-ghost: the count is honest");
    }

    /// THE RETURN RIGHT (non-vacuous, both directions): a death on a map marks THAT map and no
    /// other; the mark is un-erasable; a second mark of the same map is refused; and a mark on a
    /// living sheet is refused. The right is earned by losing there, and only there.
    #[test]
    fn the_return_right_is_earned_by_dying_there_and_never_erased() {
        let world = deploy_meta_hero(44);
        assert_eq!(tomb_days(&world), 0, "a fresh hero owes the dark nothing");

        // A LIVING hero cannot mark a map — you have to actually lose on it.
        let alive = mark_tomb_day(&world, 9);
        assert!(
            matches!(alive, Err(WorldError::Refused(_))),
            "marking a map without dying on it is refused, got {alive:?}"
        );
        assert!(!may_return_to(&world, 9), "anti-ghost: no right earned");

        progression::perish(&world).expect("a real death");
        mark_tomb_day(&world, 9).expect("day 9's map killed you — the right is earned");
        assert!(
            may_return_to(&world, 9),
            "you may go back to what killed you"
        );
        for other in [0usize, 1, 8, 10, 15] {
            assert!(
                !may_return_to(&world, other),
                "day {other} never killed you, so it is not yours to choose"
            );
        }

        // Marking the SAME map twice is a refusal, not a silent no-op (the exact FieldDelta).
        let again = mark_tomb_day(&world, 9);
        assert!(
            matches!(again, Err(WorldError::Refused(_))),
            "a map you already hold cannot be re-marked, got {again:?}"
        );

        // A second, different map stacks; the mask never loses a bit.
        mark_tomb_day(&world, 13).expect("day 13's map killed you too");
        assert!(may_return_to(&world, 9) && may_return_to(&world, 13));

        // A direct write DOWN (forgetting a death) is refused by the Monotonic mask.
        let cell = world.cell_id();
        let erase = world.apply_raw(
            &mark_tomb_day_method(9),
            vec![Effect::SetField {
                cell,
                index: TOMB_DAYS_SLOT as u64,
                value: field_from_u64(0),
            }],
        );
        assert!(
            matches!(erase, Err(WorldError::Refused(_))),
            "erasing a tomb-day is refused (Monotonic), got {erase:?}"
        );
        assert!(
            may_return_to(&world, 9) && may_return_to(&world, 13),
            "anti-ghost: the dark does not forget"
        );
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
