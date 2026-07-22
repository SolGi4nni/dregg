//! # `progression` — RPG character progression as REAL cell state on the REAL executor
//!
//! XP, LEVEL and CLASS are not app bookkeeping here — they are three (plus one)
//! register slots of a real dregg character cell, and every progression event is a
//! real cap-bounded turn the verified [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor)
//! admits IFF the installed [`CellProgram`] gate passes. The whole point: **you
//! cannot level up without earning the XP, and you cannot use a class ability out of
//! class — the referee is the kernel, not the game code.**
//!
//! ## The character cell (which fields, which teeth)
//!
//! One dregg cell = one character. Its 16 register slots carry:
//!
//! | slot | field            | tooth (executor-enforced `StateConstraint`)                     |
//! |------|------------------|-----------------------------------------------------------------|
//! | 1    | `xp`             | [`Monotonic`] (global) — XP never decreases; [`StrictMonotonic`] on a gain |
//! | 2    | `level`          | [`Monotonic`] (global) + per-level gate (below)                 |
//! | 3    | `class`          | [`WriteOnce`] (global) — set once at creation, then frozen      |
//! | 4    | `abilities_used` | [`StrictMonotonic`] on an ability use                           |
//!
//! [`Monotonic`]: dregg_app_framework::StateConstraint::Monotonic
//! [`StrictMonotonic`]: dregg_app_framework::StateConstraint::StrictMonotonic
//! [`WriteOnce`]: dregg_app_framework::StateConstraint::WriteOnce
//!
//! ## The level-up gate is an executor tooth, not an `if`
//!
//! Leveling to `L` is a real turn under the method [`level_up_method`]`(L)`. Its case
//! carries three real constraints the executor re-checks on the post-state:
//!
//! - `FieldGte { index: xp, value: `[`xp_threshold`]`(L) }` — **THE GATE**: the earned
//!   XP floor for level `L`. A level-up move without the XP fails this and is a REAL
//!   [`WorldError::Refused`](spween_dregg::WorldError) — nothing commits (anti-ghost).
//! - `FieldEquals { index: level, value: L }` — the move lands `level` at exactly `L`.
//! - `FieldDelta { index: level, delta: 1 }` — `new = old + 1`, so with the `FieldEquals`
//!   above the mover MUST have been at `L-1`: leveling is strictly sequential (no skips).
//!
//! Because the threshold is a per-level constant folded into the case guarded by that
//! level's method, the gate reads exactly "leveling to L requires XP >= threshold(L)".
//!
//! ## The class gate
//!
//! `class` is [`WriteOnce`] — [`choose_class`] sets it once at creation (a rival second
//! write is refused by the kernel). A class-locked ability move
//! ([`ability_method`]) carries `FieldEquals { index: class, value: <required class> }`:
//! the arcane bolt is admitted only when `class == MAGE`; a warrior driving it is a REAL
//! executor refusal. The ability is gated on the CLASS FIELD, in the program.
//!
//! ## Honest scope
//!
//! - XP/level/class are REAL committed cell state; progression is REAL turns; the gates
//!   are REAL executor-enforced `StateConstraint`s (driven non-vacuously in [`mod tests`]:
//!   a premature level-up and an out-of-class ability are real refusals that commit
//!   nothing; the earned ones commit and their receipts chain).
//! - This is a SINGLE character cell — one serial writer under one owner key (the same
//!   single-cell envelope the crate root's "CEILINGS" section names). Multi-character
//!   parties acting concurrently, or a level threshold that must read a peer cell, are
//!   the multi-cell frontier ([`crate::multicell`]), not this slice.
//! - The XP amounts a gain writes are driver-supplied (the character earns XP by playing);
//!   the tooth guarantees the LEDGER invariant (monotone XP, XP-gated levels, once-set
//!   class), not the game-balance of the numbers.

use std::sync::Arc;

use dregg_app_framework::{
    CellProgram, Effect, Event, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    field_from_u64, symbol,
};
use dregg_cell::program::SimpleStateConstraint;
use dregg_turn::Finality;
use spween_dregg::{CompiledStory, WorldCell, WorldError};

pub use spween_dregg::WorldCell as DungeonWorldCell;

// ── The character cell's slot layout (we author the program directly) ────────────

/// `xp` — the earned-experience slot. Globally [`Monotonic`](StateConstraint::Monotonic)
/// (never decreases); a gain is a [`StrictMonotonic`](StateConstraint::StrictMonotonic) turn.
pub const XP_SLOT: u8 = 1;
/// `level` — the character level. Globally monotone; advanced only through the XP-gated
/// per-level [`level_up_method`] cases.
pub const LEVEL_SLOT: u8 = 2;
/// `class` — the character class id ([`WARRIOR`]/[`MAGE`]/[`ROGUE`]). Globally
/// [`WriteOnce`](StateConstraint::WriteOnce): set once at creation, then frozen.
pub const CLASS_SLOT: u8 = 3;
/// `abilities_used` — a real counter a class ability advances ([`StrictMonotonic`]).
pub const ABILITY_SLOT: u8 = 4;
/// `dead` — the HARDCORE death flag (`0` alive, `1` dead). Globally
/// [`WriteOnce`](StateConstraint::WriteOnce): a hardcore death is FINAL — once set it can
/// never be un-set (a resurrection is a real executor refusal), and while set the earn /
/// level-up cases are gated shut (`FieldEquals(dead, 0)`), so a dead character's run is
/// over on the ledger. A non-hardcore character simply never sets it (it stays `0`, the
/// WriteOnce passes idempotently). This is what lets a no-cheat leaderboard PROVE
/// "survived / deepest depth / no-death streak".
pub const DEAD_SLOT: u8 = 5;

// ── Class ids ────────────────────────────────────────────────────────────────────

/// The Warrior class id (shield-bash locked).
pub const WARRIOR: u64 = 1;
/// The Mage class id (arcane-bolt locked).
pub const MAGE: u64 = 2;
/// The Rogue class id.
pub const ROGUE: u64 = 3;

/// The highest level the progression program installs a gate for.
pub const MAX_LEVEL: u64 = 5;

/// The earned-XP floor required to reach level `L` — the constant the executor's
/// `FieldGte(xp, .)` gate on `level_up_to_L` enforces. A real (rising) RPG curve;
/// `L <= 1` needs nothing (you start at level 1).
pub fn xp_threshold(level: u64) -> u64 {
    match level {
        0 | 1 => 0,
        2 => 100,
        3 => 250,
        4 => 450,
        5 => 700,
        // Beyond the installed ceiling: unreachable (no case), name a large floor.
        _ => u64::MAX,
    }
}

// ── Turn method names (the driver + the program agree on these) ──────────────────

/// The method a [`gain_xp`] turn presents (gated by [`StrictMonotonic`] on `xp`).
pub const GAIN_XP_METHOD: &str = "hero/gain_xp";
/// Dedicated executor method for one exact private-Bazaar reward.  The turn
/// emits [`PRIVATE_BAZAAR_XP_EVENT`] with the operation id and exact XP delta,
/// so a durable recovery path can distinguish this consequence from every
/// other monotone XP turn without trusting a caller's description.
pub const PRIVATE_BAZAAR_XP_METHOD: &str = "hero/gain_xp/private-bazaar/v1";
pub const PRIVATE_BAZAAR_XP_EVENT: &str = "hero/event/private-bazaar-xp/v1";

/// Canonical event symbol pinned by private-Bazaar deployment policy. Keeping
/// this derivation beside the game vocabulary prevents frontends from
/// reimplementing the string-to-symbol mapping.
pub fn private_bazaar_xp_event_topic() -> [u8; 32] {
    symbol(PRIVATE_BAZAAR_XP_EVENT)
}
/// The method a [`choose_class`] turn presents (the class-setting creation move).
pub const CHOOSE_CLASS_METHOD: &str = "hero/choose_class";
/// The method a HARDCORE death presents ([`perish`]): sets `dead = 1` under the global
/// `WriteOnce(dead)` — a first death (0→1) commits, and it can never be undone.
pub const HARDCORE_PERISH_METHOD: &str = "hero/perish";
/// The method a resurrection ATTEMPT presents ([`attempt_resurrect`]): tries to write
/// `dead = 0`. On a dead character this is a real executor refusal (the global
/// `WriteOnce(dead)` bars the 1→0 change) — hardcore death is final.
pub const HARDCORE_RESURRECT_METHOD: &str = "hero/resurrect";

/// The method a level-up-to-`level` turn presents. The case guarded by this method
/// carries the `FieldGte(xp, xp_threshold(level))` gate.
pub fn level_up_method(level: u64) -> String {
    format!("hero/level_up_to_{level}")
}

/// The method a class ability presents. `class_id` names which class the ability is
/// locked to (the case carries `FieldEquals(class, class_id)`).
pub fn ability_method(class_id: u64) -> String {
    format!("hero/ability/{class_id}")
}

/// The Mage's arcane-bolt ability method (locked to [`MAGE`]).
pub fn arcane_bolt_method() -> String {
    ability_method(MAGE)
}
/// The Warrior's shield-bash ability method (locked to [`WARRIOR`]).
pub fn shield_bash_method() -> String {
    ability_method(WARRIOR)
}

/// The scene id that drives the character cell's deterministic identity.
pub const HERO_SCENE_ID: &str = "dungeon-on-dregg/hero-progression/v1";

/// **Build the character cell's [`CompiledStory`]** — the slot layout plus the
/// executor-enforced progression program. Authored directly (this is a character
/// sheet, not a passage graph), the program is a real [`CellProgram::Cases`] the
/// [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor) enforces move-for-move.
///
/// The cases:
/// 1. **Global invariants** (an `Always` guard, ANDed onto every turn): `xp` and
///    `level` [`Monotonic`](StateConstraint::Monotonic) (neither ever decreases) and
///    `class` [`WriteOnce`](StateConstraint::WriteOnce) (set once, then frozen).
/// 2. **`gain_xp`**: `xp` must [`StrictMonotonic`](StateConstraint::StrictMonotonic)ally
///    increase — a gain is a real positive gain.
/// 3. **`choose_class`**: the written class must be one of the three valid ids
///    (`AnyOf[FieldEquals(class, WARRIOR|MAGE|ROGUE)]`); the global `WriteOnce` makes it
///    a one-time creation move.
/// 4. **`level_up_to_L`** for `L` in `2..=MAX_LEVEL`: `FieldGte(xp, xp_threshold(L))`
///    (the earned-XP gate) + `FieldEquals(level, L)` + `FieldDelta(level, +1)` (lands at
///    exactly `L`, one step from `L-1`).
/// 5. **`ability/<class>`**: `FieldEquals(class, <class>)` (locked to that class) +
///    `StrictMonotonic(abilities_used)` (the ability advances a real counter).
pub fn hero_story() -> CompiledStory {
    let mut cases = Vec::new();

    // 1. Global invariants — ANDed onto every admitted turn.
    cases.push(TransitionCase {
        guard: TransitionGuard::Always,
        constraints: vec![
            StateConstraint::Monotonic { index: XP_SLOT },
            StateConstraint::Monotonic { index: LEVEL_SLOT },
            StateConstraint::WriteOnce { index: CLASS_SLOT },
            // HARDCORE: death is WriteOnce-final. A non-hardcore character never sets
            // `dead`, so this passes idempotently (0→0); a hardcore death (0→1) commits
            // once and can never be undone (a 1→0 resurrection is refused).
            StateConstraint::WriteOnce { index: DEAD_SLOT },
        ],
    });

    // 2. gain_xp — a real, strictly-positive XP gain, and ONLY while alive (a dead
    //    hardcore character earns nothing — the run is over on the ledger).
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(GAIN_XP_METHOD),
        },
        constraints: vec![
            StateConstraint::StrictMonotonic { index: XP_SLOT },
            StateConstraint::FieldEquals {
                index: DEAD_SLOT,
                value: field_from_u64(0),
            },
        ],
    });

    // Private Bazaar rewards have the same ledger invariant as an ordinary XP
    // gain, but a distinct method identity.  Their exact operation id and
    // reward opening are committed by an EmitEvent in the same executor turn.
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(PRIVATE_BAZAAR_XP_METHOD),
        },
        constraints: vec![
            StateConstraint::StrictMonotonic { index: XP_SLOT },
            StateConstraint::FieldEquals {
                index: DEAD_SLOT,
                value: field_from_u64(0),
            },
        ],
    });

    // 3. choose_class — the class must be a valid id; global WriteOnce makes it once.
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(CHOOSE_CLASS_METHOD),
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

    // 4. level_up_to_L — the XP-gated, sequential per-level cases. Level 1 is reached
    //    from the fresh level-0 cell for free (`xp_threshold(1) == 0`); levels 2.. gate
    //    on a real earned-XP floor.
    for level in 1..=MAX_LEVEL {
        cases.push(TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(&level_up_method(level)),
            },
            constraints: vec![
                // THE GATE: the earned-XP floor for this level.
                StateConstraint::FieldGte {
                    index: XP_SLOT,
                    value: field_from_u64(xp_threshold(level)),
                },
                // Lands `level` at exactly L...
                StateConstraint::FieldEquals {
                    index: LEVEL_SLOT,
                    value: field_from_u64(level),
                },
                // ...one step up from L-1 (no skipping).
                StateConstraint::FieldDelta {
                    index: LEVEL_SLOT,
                    delta: field_from_u64(1),
                },
                // ...and only while alive (a dead hardcore character cannot level).
                StateConstraint::FieldEquals {
                    index: DEAD_SLOT,
                    value: field_from_u64(0),
                },
            ],
        });
    }

    // 4b. THE SLOT-BOUND LEVEL GATE — the tooth that makes the XP floor real.
    //
    // The per-level `MethodIs{level_up_to_L}` cases (case 4) gate only turns that PRESENT a
    // level-up method. But `apply_raw` is public: a client can staple `SetField(level, 5)` onto ANY
    // other method's turn (e.g. a legitimate `hero/gain_xp`), where no `level_up_to_L` case matches
    // and the only non-dispatching guard on `level` is the global `Always Monotonic{level}` — which
    // happily admits a jump 0 -> 5. So a level lands with NO earned-XP floor and NO +1 step.
    // (Driven: `a_stapled_level_write_cannot_ride_another_methods_turn`, which committed level 5
    // with 0 XP before this case existed.)
    //
    // `SlotChanged{level}` binds the gates to the WRITE. Because the executor runs EVERY matching
    // case (`cell/src/program/eval.rs:104-120`), these compose with the authoring method's own
    // constraints. Two teeth:
    //   * `FieldDelta{level, +1}` — a level moves up EXACTLY one step per turn (no skipping).
    //   * for each L, the implication `level == L  ->  xp >= xp_threshold(L)`, expressed as
    //     `AnyOf{ Not(level == L), xp >= t(L) }`. The `AnyOf` variants AND together across L, and
    //     the new level is a single value V, so only the V-th implication is load-bearing (it forces
    //     `xp >= t(V)`); every other L is discharged by its `Not(level == L)` branch. This is the
    //     exact per-level earned-XP floor, now bound to the write instead of the method.
    // `SlotChanged` is NOT method-dispatching, so default-deny is unaffected.
    let mut level_gate: Vec<StateConstraint> = vec![
        StateConstraint::FieldEquals {
            index: DEAD_SLOT,
            value: field_from_u64(0),
        },
        StateConstraint::FieldDelta {
            index: LEVEL_SLOT,
            delta: field_from_u64(1),
        },
    ];
    for level in 1..=MAX_LEVEL {
        level_gate.push(StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                    index: LEVEL_SLOT,
                    value: field_from_u64(level),
                })),
                SimpleStateConstraint::FieldGte {
                    index: XP_SLOT,
                    value: field_from_u64(xp_threshold(level)),
                },
            ],
        });
    }
    cases.push(TransitionCase {
        guard: TransitionGuard::SlotChanged { index: LEVEL_SLOT },
        constraints: level_gate,
    });

    // 5. class-locked abilities — admitted only in the right class.
    for class_id in [WARRIOR, MAGE, ROGUE] {
        cases.push(TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(&ability_method(class_id)),
            },
            constraints: vec![
                StateConstraint::FieldEquals {
                    index: CLASS_SLOT,
                    value: field_from_u64(class_id),
                },
                StateConstraint::StrictMonotonic {
                    index: ABILITY_SLOT,
                },
            ],
        });
    }

    // 6. HARDCORE death (perish) — sets `dead = 1`; the global `WriteOnce(dead)` makes it
    //    a one-time, un-undoable write. 7. resurrect ATTEMPT — writes `dead = 0`; on a
    //    dead character the global WriteOnce bars the 1→0 change (a real refusal).
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(HARDCORE_PERISH_METHOD),
        },
        constraints: vec![StateConstraint::FieldEquals {
            index: DEAD_SLOT,
            value: field_from_u64(1),
        }],
    });
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(HARDCORE_RESURRECT_METHOD),
        },
        constraints: vec![StateConstraint::FieldEquals {
            index: DEAD_SLOT,
            value: field_from_u64(0),
        }],
    });

    CompiledStory {
        scene_id: HERO_SCENE_ID.to_string(),
        var_slots: [
            ("xp".to_string(), XP_SLOT as u64),
            ("level".to_string(), LEVEL_SLOT as u64),
            ("class".to_string(), CLASS_SLOT as u64),
            ("abilities_used".to_string(), ABILITY_SLOT as u64),
            ("dead".to_string(), DEAD_SLOT as u64),
        ]
        .into_iter()
        .collect(),
        has_slots: Default::default(),
        passage_index: Default::default(),
        program: CellProgram::Cases(cases),
        fully_gated: Default::default(),
    }
}

/// **Deploy a fresh character** as a real world-cell with the progression program
/// installed. Deterministic in `seed` (re-deploy reproduces the same identity + state
/// hashes, what the replay verifier leans on). The character begins at level 0 / xp 0 /
/// no class; [`choose_class`] + [`level_up`] advance it through real turns.
pub fn deploy_hero(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(hero_story()), seed).expect("the character cell deploys")
}

// ── The progression turns (each ONE real cap-bounded turn) ───────────────────────

/// **Set the character's class** — the one-time creation move. A real turn under
/// [`CHOOSE_CLASS_METHOD`] writing `class = class_id`; the global
/// [`WriteOnce`](StateConstraint::WriteOnce) tooth admits the first write and REFUSES a
/// later re-class (nothing commits).
pub fn choose_class(world: &WorldCell, class_id: u64) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    world.apply_raw(
        CHOOSE_CLASS_METHOD,
        vec![Effect::SetField {
            cell,
            index: CLASS_SLOT as u64,
            value: field_from_u64(class_id),
        }],
    )
}

/// **Earn XP** — a real turn under [`GAIN_XP_METHOD`] writing `xp += amount`. The
/// executor's [`StrictMonotonic`](StateConstraint::StrictMonotonic) tooth (plus the
/// global `Monotonic`) admits it because a gain strictly raises the earned-XP slot; XP
/// can never move the other way.
pub fn gain_xp(world: &WorldCell, amount: u64) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    let new_xp = world.read_var("xp") + amount;
    world.apply_raw(
        GAIN_XP_METHOD,
        vec![Effect::SetField {
            cell,
            index: XP_SLOT as u64,
            value: field_from_u64(new_xp),
        }],
    )
}

/// Apply one exact, operation-addressed Dark Bazaar XP consequence.
///
/// `expected_before` is part of the prepared outbox intent.  A stale or replayed
/// dispatch refuses before the executor runs; the caller cannot turn the same
/// authorization into a second additive grant.  The event and the XP write are
/// effects of the same cap-bounded turn and therefore share one signed/final
/// receipt.
pub fn gain_private_bazaar_xp(
    world: &WorldCell,
    operation_id: [u8; 32],
    expected_before: u64,
    amount: u64,
) -> Result<TurnReceipt, WorldError> {
    let observed = world.read_var("xp");
    if observed != expected_before {
        return Err(WorldError::Refused(format!(
            "private Bazaar XP expected pre-value {expected_before}, observed {observed}"
        )));
    }
    let expected_after = expected_before
        .checked_add(amount)
        .ok_or_else(|| WorldError::Refused("private Bazaar XP overflow".to_owned()))?;
    let cell = world.cell_id();
    world.apply_raw(
        PRIVATE_BAZAAR_XP_METHOD,
        vec![
            Effect::SetField {
                cell,
                index: XP_SLOT as u64,
                value: field_from_u64(expected_after),
            },
            Effect::EmitEvent {
                cell,
                event: Event::new(
                    symbol(PRIVATE_BAZAAR_XP_EVENT),
                    private_bazaar_event_data(
                        operation_id,
                        expected_before,
                        amount,
                        expected_after,
                    ),
                ),
            },
        ],
    )
}

/// Verify that `receipt` is the finalized, executor-signed result of the exact
/// dedicated reward turn.  This is the minting predicate for the Bazaar's
/// opaque committed-effect authority immediately after dispatch.  Recovery of
/// an older receipt uses [`verify_private_bazaar_xp_receipt_evidence`] instead:
/// a later legitimate hero turn may have advanced the current XP head, but it
/// cannot alter this signed historical receipt.
pub fn verify_private_bazaar_xp_receipt(
    world: &WorldCell,
    receipt: &TurnReceipt,
    executor_pubkey: [u8; 32],
    expected_federation: [u8; 32],
    operation_id: [u8; 32],
    expected_before: u64,
    amount: u64,
) -> bool {
    let Some(expected_after) = expected_before.checked_add(amount) else {
        return false;
    };
    verify_private_bazaar_xp_receipt_evidence(
        world,
        receipt,
        executor_pubkey,
        expected_federation,
        operation_id,
        expected_before,
        amount,
    ) && world.read_var("xp") == expected_after
}

/// Verify the immutable evidence in one historical Bazaar XP receipt without
/// requiring that receipt's post-state to remain the world's current head.
///
/// This is recovery-only evidence: the caller must obtain `receipt` from the
/// target world's authoritative receipt chain.  The immediate dispatch path
/// must use [`verify_private_bazaar_xp_receipt`], which additionally checks the
/// live postcondition before recording `Applied`.
pub fn verify_private_bazaar_xp_receipt_evidence(
    world: &WorldCell,
    receipt: &TurnReceipt,
    executor_pubkey: [u8; 32],
    expected_federation: [u8; 32],
    operation_id: [u8; 32],
    expected_before: u64,
    amount: u64,
) -> bool {
    let Some(expected_after) = expected_before.checked_add(amount) else {
        return false;
    };
    let expected_data =
        private_bazaar_event_data(operation_id, expected_before, amount, expected_after);
    receipt.finality == Finality::Final
        && receipt.federation_id == expected_federation
        && receipt.action_count == 1
        && receipt.turn_hash != [0; 32]
        && receipt.effects_hash != [0; 32]
        && receipt.pre_state_hash != receipt.post_state_hash
        && receipt.executor_signature.is_some()
        && dregg_turn::verify_receipt_signature_with_keys(receipt, &[executor_pubkey]).is_ok()
        && receipt.emitted_events.iter().any(|event| {
            event.cell == world.cell_id()
                && event.topic == symbol(PRIVATE_BAZAAR_XP_EVENT)
                && event.data == expected_data
        })
        && receipt
            .emitted_events
            .iter()
            .filter(|event| event.topic == symbol(PRIVATE_BAZAAR_XP_EVENT))
            .count()
            == 1
}

fn private_bazaar_event_data(
    operation_id: [u8; 32],
    expected_before: u64,
    amount: u64,
    expected_after: u64,
) -> Vec<dregg_app_framework::FieldElement> {
    let mut data = Vec::with_capacity(11);
    for chunk in operation_id.chunks_exact(4) {
        data.push(field_from_u64(u32::from_be_bytes(
            chunk.try_into().expect("four-byte operation-id lane"),
        ) as u64));
    }
    data.push(field_from_u64(expected_before));
    data.push(field_from_u64(amount));
    data.push(field_from_u64(expected_after));
    data
}

/// **Level up by one** — a real turn under `level_up_to_(current+1)`. Writes `level` to
/// the next level; the executor GATES it on `FieldGte(xp, xp_threshold(next))`. Without
/// the earned XP the kernel REFUSES the turn (a real [`WorldError::Refused`]) and nothing
/// commits — you cannot level without the XP. Returns the target level on commit.
pub fn level_up(world: &WorldCell) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    let target = world.read_var("level") + 1;
    world.apply_raw(
        &level_up_method(target),
        vec![Effect::SetField {
            cell,
            index: LEVEL_SLOT as u64,
            value: field_from_u64(target),
        }],
    )
}

/// **Use a class-locked ability** — a real turn under [`ability_method`]`(class_id)`
/// advancing the `abilities_used` counter. The executor admits it ONLY when the
/// character's `class` slot equals `class_id` (`FieldEquals(class, class_id)`); an
/// out-of-class caller is a real [`WorldError::Refused`] (nothing commits).
pub fn use_ability(world: &WorldCell, class_id: u64) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    let next = world.read_var("abilities_used") + 1;
    world.apply_raw(
        &ability_method(class_id),
        vec![Effect::SetField {
            cell,
            index: ABILITY_SLOT as u64,
            value: field_from_u64(next),
        }],
    )
}

/// **Kill the character (HARDCORE) — a real committed DEATH turn.** Writes `dead = 1`
/// under [`HARDCORE_PERISH_METHOD`]; the global [`WriteOnce`](StateConstraint::WriteOnce)
/// on the `dead` slot makes this a one-time write. A hardcore run that ends in defeat
/// fires this, recording an un-forgeable, un-undoable death on the character's ledger.
pub fn perish(world: &WorldCell) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    world.apply_raw(
        HARDCORE_PERISH_METHOD,
        vec![Effect::SetField {
            cell,
            index: DEAD_SLOT as u64,
            value: field_from_u64(1),
        }],
    )
}

/// **Attempt a resurrection** — a real turn under [`HARDCORE_RESURRECT_METHOD`] writing
/// `dead = 0`. On a DEAD character the global `WriteOnce(dead)` bars the 1→0 change and
/// the executor REFUSES it (nothing commits): hardcore death is FINAL. (On a live
/// character the write is a 0→0 no-op that commits — there is nothing to resurrect.)
pub fn attempt_resurrect(world: &WorldCell) -> Result<TurnReceipt, WorldError> {
    let cell = world.cell_id();
    world.apply_raw(
        HARDCORE_RESURRECT_METHOD,
        vec![Effect::SetField {
            cell,
            index: DEAD_SLOT as u64,
            value: field_from_u64(0),
        }],
    )
}

/// Whether the character is (hardcore-)dead — the committed `dead` flag is set.
pub fn is_dead(world: &WorldCell) -> bool {
    world.read_var("dead") != 0
}

/// Introspect the executor-enforced constraints installed on the case guarded by
/// `method` — proof each progression rule is a real kernel predicate (for the example
/// to print the actual `FieldGte`/`WriteOnce`/`FieldEquals` teeth verbatim).
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

    /// The level-up gate lowers to a REAL `FieldGte` tooth on the XP slot — the earned-XP
    /// floor is a kernel predicate keyed by the level's method, not app bookkeeping.
    #[test]
    fn level_up_gate_is_a_real_fieldgte_on_xp() {
        let story = hero_story();
        for level in 2..=MAX_LEVEL {
            let cs = case_constraints(&story, &level_up_method(level));
            assert!(
                cs.iter().any(|c| matches!(
                    c,
                    StateConstraint::FieldGte { index, value }
                        if *index == XP_SLOT && *value == field_from_u64(xp_threshold(level))
                )),
                "level_up_to_{level} carries FieldGte(xp, {}); got {cs:?}",
                xp_threshold(level)
            );
        }
        // The class ability is gated on the CLASS field with a real FieldEquals.
        let ab = case_constraints(&story, &arcane_bolt_method());
        assert!(
            ab.iter().any(|c| matches!(
                c,
                StateConstraint::FieldEquals { index, value }
                    if *index == CLASS_SLOT && *value == field_from_u64(MAGE)
            )),
            "arcane bolt is gated FieldEquals(class, MAGE); got {ab:?}"
        );
    }

    /// XP GAIN is a real committed turn and the XP slot is monotone: two gains commit
    /// (0 → 60 → 130) and their receipts chain (`pre == prev.post`).
    #[test]
    fn xp_gain_commits_and_is_monotone() {
        let world = deploy_hero(1);
        assert_eq!(world.read_var("xp"), 0, "a fresh hero has no XP");

        let r1 = gain_xp(&world, 60).expect("earning 60 XP commits");
        assert_eq!(world.read_var("xp"), 60);
        let r2 = gain_xp(&world, 70).expect("earning 70 more XP commits");
        assert_eq!(world.read_var("xp"), 130);

        assert_ne!(
            r1.turn_hash, [0u8; 32],
            "XP gain is a genuine committed turn"
        );
        assert_eq!(
            r2.pre_state_hash, r1.post_state_hash,
            "the XP-gain receipts chain (pre == prev.post)"
        );
    }

    #[test]
    fn private_bazaar_xp_is_exact_signed_final_and_recoverable_by_receipt() {
        let world = deploy_hero(0xB4);
        world.set_executor_signing_key([0xA7; 32]);
        let executor_pubkey = world.executor_pubkey().expect("signer installed");
        let operation_id = [0x51; 32];

        let receipt =
            gain_private_bazaar_xp(&world, operation_id, 0, 144).expect("the exact reward commits");
        assert_eq!(world.read_var("xp"), 144);
        assert!(verify_private_bazaar_xp_receipt(
            &world,
            &receipt,
            executor_pubkey,
            world.federation_id(),
            operation_id,
            0,
            144,
        ));
        assert!(!verify_private_bazaar_xp_receipt(
            &world,
            &receipt,
            executor_pubkey,
            world.federation_id(),
            operation_id,
            0,
            145,
        ));
        assert_eq!(
            world
                .receipt_by_hash(receipt.receipt_hash())
                .expect("authoritative receipt lookup")
                .receipt_hash(),
            receipt.receipt_hash()
        );

        let replay = gain_private_bazaar_xp(&world, operation_id, 0, 144);
        assert!(
            matches!(replay, Err(WorldError::Refused(_))),
            "the prepared absolute pre-state makes a second additive grant impossible"
        );
        assert_eq!(world.read_var("xp"), 144);

        gain_xp(&world, 1).expect("a later legitimate hero turn advances the head");
        assert_eq!(world.read_var("xp"), 145);
        assert!(verify_private_bazaar_xp_receipt_evidence(
            &world,
            &receipt,
            executor_pubkey,
            world.federation_id(),
            operation_id,
            0,
            144,
        ));
        assert!(
            !verify_private_bazaar_xp_receipt(
                &world,
                &receipt,
                executor_pubkey,
                world.federation_id(),
                operation_id,
                0,
                144,
            ),
            "the immediate verifier intentionally requires the receipt post-state to remain head"
        );
    }

    /// THE HARD GATE (premature level-up): a character with too little XP is REFUSED by
    /// the executor's `FieldGte` gate — a real `WorldError::Refused` that commits nothing
    /// (anti-ghost: still level 1, XP untouched). The SAME move commits once the XP is
    /// earned. Non-vacuous: the identical move is refused then admitted, XP the only
    /// difference.
    #[test]
    fn premature_level_up_is_refused_earned_level_up_commits() {
        let world = deploy_hero(2);
        choose_class(&world, WARRIOR).expect("choosing a class at creation commits");
        // Reach level 1 first (from level 0, threshold(1) == 0, no XP needed).
        level_up(&world).expect("reaching level 1 needs no XP");
        assert_eq!(world.read_var("level"), 1);

        // Earn SOME XP, but not enough for level 2 (needs 100).
        gain_xp(&world, 50).expect("earning 50 XP commits");
        assert_eq!(world.read_var("xp"), 50);

        // PREMATURE: leveling to 2 needs xp >= 100; with 50 it is a REAL refusal.
        let refused = level_up(&world);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a level-up without the earned XP is refused by the executor, got {refused:?}"
        );
        // Anti-ghost: the refused turn committed NOTHING.
        assert_eq!(
            world.read_var("level"),
            1,
            "still level 1 after the refusal"
        );
        assert_eq!(world.read_var("xp"), 50, "XP untouched by the refused turn");

        // Now EARN the rest of the XP and drive the SAME move — it commits.
        gain_xp(&world, 60).expect("earning 60 more XP commits");
        assert_eq!(world.read_var("xp"), 110, "now over the level-2 floor");
        let r = level_up(&world).expect("with 110 XP >= 100, the level-up commits");
        assert_eq!(world.read_var("level"), 2, "leveled up to 2");
        assert_ne!(
            r.turn_hash, [0u8; 32],
            "the level-up is a genuine committed turn"
        );
    }

    /// A monotone / sequential ladder: with enough XP, levels 1→2→3 commit in order and
    /// the receipts chain. Skipping is refused — from level 2 you cannot jump to level 4
    /// (the `level_up_to_4` case's `FieldDelta(level,+1)` requires old == 3).
    #[test]
    fn levels_climb_sequentially_and_skips_are_refused() {
        let world = deploy_hero(3);
        choose_class(&world, ROGUE).expect("class");
        level_up(&world).expect("level 1");
        gain_xp(&world, 300).expect("earn 300 XP"); // over the level-3 floor (250)

        let r2 = level_up(&world).expect("level 2 (xp 300 >= 100)");
        assert_eq!(world.read_var("level"), 2);
        let r3 = level_up(&world).expect("level 3 (xp 300 >= 250)");
        assert_eq!(world.read_var("level"), 3);
        assert_eq!(
            r3.pre_state_hash, r2.post_state_hash,
            "the level-up receipts chain"
        );

        // Try to SKIP to level 4 by presenting the level_up_to_4 method while at level 3
        // — wait, that IS the next level, so it should work; instead prove a SKIP from 3
        // to 5 is refused (level_up_to_5 needs old == 4 via FieldDelta, and xp < 700 too).
        let cell = world.cell_id();
        let skip = world.apply_raw(
            &level_up_method(5),
            vec![Effect::SetField {
                cell,
                index: LEVEL_SLOT as u64,
                value: field_from_u64(5),
            }],
        );
        assert!(
            matches!(skip, Err(WorldError::Refused(_))),
            "skipping 3 -> 5 is refused (FieldDelta requires one step, XP below the floor), got {skip:?}"
        );
        assert_eq!(world.read_var("level"), 3, "anti-ghost: still level 3");
    }

    /// CLASS is WriteOnce: set once at creation, a re-class is a REAL executor refusal.
    #[test]
    fn class_is_write_once() {
        let world = deploy_hero(4);
        choose_class(&world, MAGE).expect("choosing Mage at creation commits");
        assert_eq!(world.read_var("class"), MAGE);

        let refused = choose_class(&world, WARRIOR);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "re-classing is refused (WriteOnce), got {refused:?}"
        );
        assert_eq!(world.read_var("class"), MAGE, "anti-ghost: still a Mage");
    }

    /// THE CLASS GATE (both directions, non-vacuous): the arcane bolt is ADMITTED for a
    /// Mage and REFUSED for a Warrior — the SAME ability move, gated on the class field.
    #[test]
    fn class_ability_admitted_for_right_class_refused_for_wrong() {
        // A Mage casts the arcane bolt — admitted (class == MAGE).
        let mage = deploy_hero(5);
        choose_class(&mage, MAGE).expect("Mage");
        let r = use_ability(&mage, MAGE).expect("a Mage may cast the arcane bolt");
        assert_eq!(
            mage.read_var("abilities_used"),
            1,
            "the ability advanced a real counter"
        );
        assert_ne!(r.turn_hash, [0u8; 32]);

        // A Warrior drives the SAME arcane-bolt method — REFUSED (class != MAGE).
        let warrior = deploy_hero(6);
        choose_class(&warrior, WARRIOR).expect("Warrior");
        let refused = use_ability(&warrior, MAGE);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a Warrior casting the Mage's arcane bolt is refused, got {refused:?}"
        );
        assert_eq!(
            warrior.read_var("abilities_used"),
            0,
            "anti-ghost: nothing committed for the out-of-class ability"
        );

        // And the Warrior's OWN ability (shield bash) is admitted for the Warrior.
        let r = use_ability(&warrior, WARRIOR).expect("a Warrior may shield-bash");
        assert_eq!(warrior.read_var("abilities_used"), 1);
        assert_ne!(r.turn_hash, [0u8; 32]);
    }

    /// HARDCORE death is WriteOnce-FINAL (non-vacuous). A living character earns and
    /// commits; a real `perish` turn sets `dead = 1`; then a resurrection is a REAL
    /// executor refusal (WriteOnce bars 1→0) AND a dead character earns nothing (the
    /// earn case is gated `FieldEquals(dead, 0)`). The death is an un-forgeable,
    /// un-undoable committed fact — the leaderboard's no-death proof.
    #[test]
    fn hardcore_death_is_writeonce_final() {
        let world = deploy_hero(20);
        choose_class(&world, WARRIOR).expect("class");
        gain_xp(&world, 40).expect("a living character earns");
        assert_eq!(world.read_var("xp"), 40);
        assert!(!is_dead(&world), "alive so far");

        // The hardcore death — a real committed turn (0→1).
        let d = perish(&world).expect("the death turn commits");
        assert_ne!(d.turn_hash, [0u8; 32]);
        assert!(is_dead(&world), "the character is dead");

        // A resurrection is REFUSED (WriteOnce bars the 1→0 change) — death is final.
        let res = attempt_resurrect(&world);
        assert!(
            matches!(res, Err(WorldError::Refused(_))),
            "resurrecting a dead character is refused (WriteOnce), got {res:?}"
        );
        assert!(is_dead(&world), "anti-ghost: still dead");

        // A dead character earns NOTHING — the earn case is gated on being alive.
        let earn = gain_xp(&world, 100);
        assert!(
            matches!(earn, Err(WorldError::Refused(_))),
            "a dead character cannot earn XP, got {earn:?}"
        );
        assert_eq!(world.read_var("xp"), 40, "anti-ghost: XP frozen at death");

        // A SECOND perish is idempotent (1→1, WriteOnce admits an unchanged write).
        perish(&world).expect("a re-perish is an idempotent no-op");
        assert!(is_dead(&world));
    }

    /// THE SLOT-BOUND LEVEL TOOTH (the falsifier for a real hole): a `level` write STAPLED onto a
    /// DIFFERENT method's legitimate turn cannot buy a level without the earned XP.
    ///
    /// `apply_raw` is public, so a client can append `SetField(level, 5)` to a turn it is otherwise
    /// entitled to make. Before the `SlotChanged{level}` case existed, the per-level XP floor lived
    /// ONLY on the `level_up_to_L` cases, while the global `Always Monotonic{level}` admitted a jump
    /// 0 -> 5 on any method. DRIVEN, a `SetField(level, 5)` stapled onto a legitimate `hero/gain_xp`
    /// committed **level 5 with 0 XP** (`xp_threshold(5) == 700`).
    #[test]
    fn a_stapled_level_write_cannot_ride_another_methods_turn() {
        let world = deploy_hero(41);
        choose_class(&world, WARRIOR).expect("class");
        let cell = world.cell_id();

        // A legitimate gain_xp payload (xp 0 -> 1, strictly monotone, alive) plus a stapled jump to
        // the max level — far short of xp_threshold(5) == 700.
        let jump = world.apply_raw(
            GAIN_XP_METHOD,
            vec![
                Effect::SetField {
                    cell,
                    index: XP_SLOT as u64,
                    value: field_from_u64(1),
                },
                Effect::SetField {
                    cell,
                    index: LEVEL_SLOT as u64,
                    value: field_from_u64(MAX_LEVEL),
                },
            ],
        );
        assert!(
            matches!(jump, Err(WorldError::Refused(_))),
            "a level jump stapled onto gain_xp must be REFUSED (no earned XP, no +1 step); got {jump:?}"
        );
        assert_eq!(world.read_var("level"), 0, "anti-ghost: no free level");
        assert_eq!(
            world.read_var("xp"),
            0,
            "anti-ghost: the refusal committed nothing"
        );

        // Even a single +1 step is refused when the XP floor for that level is unmet: reach level 1
        // for free (threshold 0), then try to staple level 2 (needs 100 XP) onto a gain_xp of 1.
        level_up(&world).expect("free level 1");
        let step = world.apply_raw(
            GAIN_XP_METHOD,
            vec![
                Effect::SetField {
                    cell,
                    index: XP_SLOT as u64,
                    value: field_from_u64(1),
                },
                Effect::SetField {
                    cell,
                    index: LEVEL_SLOT as u64,
                    value: field_from_u64(2),
                },
            ],
        );
        assert!(
            matches!(step, Err(WorldError::Refused(_))),
            "a +1 level step below the XP floor (1 < 100) is refused too, got {step:?}"
        );
        assert_eq!(world.read_var("level"), 1, "anti-ghost: still level 1");

        // THE GATE IS AN XP FLOOR, NOT A BAN: with the earned XP the legit level-up commits.
        gain_xp(&world, 120).expect("earn the XP");
        level_up(&world).expect("a legitimately-earned level 2 still commits");
        assert_eq!(world.read_var("level"), 2, "the real level landed");
    }

    /// A full progression arc is a real receipt chain: choose class → earn XP → level up
    /// → use a class ability. Every step chains `pre == prev.post` (one serial writer,
    /// one character cell).
    #[test]
    fn a_full_progression_arc_is_a_real_receipt_chain() {
        let world = deploy_hero(7);
        let r0 = choose_class(&world, MAGE).expect("choose class");
        let r1 = level_up(&world).expect("reach level 1");
        let r2 = gain_xp(&world, 120).expect("earn XP");
        let r3 = level_up(&world).expect("level up to 2 (120 >= 100)");
        let r4 = use_ability(&world, MAGE).expect("cast the arcane bolt as a Mage");

        for (a, b) in [(&r0, &r1), (&r1, &r2), (&r2, &r3), (&r3, &r4)] {
            assert_eq!(
                b.pre_state_hash, a.post_state_hash,
                "the progression receipts chain: pre == prev.post"
            );
        }
        assert_eq!(world.read_var("class"), MAGE);
        assert_eq!(world.read_var("level"), 2);
        assert_eq!(world.read_var("xp"), 120);
        assert_eq!(world.read_var("abilities_used"), 1);
    }
}
