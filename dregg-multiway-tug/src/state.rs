//! # The state declaration + the hand-rolled play teeth.
//!
//! The multiway-tug STATE is declared as a [`dregg_schema::Schema`] and lowered by the
//! CONSUMED dregg-schema allocator ([`dregg_schema::layout::allocate_checked`]) to a
//! Legal (disjoint + in-bounds, the RotatedLayout discipline) slot/heap layout: the 16
//! scalar counters/win-registers land in the register file, the 8 used-flags + 14
//! per-guild placement scores land on heap keys `16..37`.
//!
//! The PLAY TEETH are then hand-rolled as a [`CellProgram::Cases`] over those
//! allocator-resolved slots (the portfolio's custom-transition shape — these teeth go
//! beyond the five schema archetypes, so we author the `Cases` directly rather than call
//! `emit_program`). Each action method carries:
//!
//! * **21-card conservation** — `SumEquals` over the eight card-zone counters `== 21`, on
//!   EVERY move post-state. A play that conjures or destroys a favor breaks the sum and is
//!   refused.
//! * **one-action-per-round** — `HeapAtom::WriteOnce` on each `(player, action)` used-flag
//!   (written with the round's strictly-increasing action stamp, so any reuse changes the
//!   frozen flag and is refused).
//! * **monotone scores** — `HeapAtom::Monotonic` on each per-guild placement counter (a
//!   placed favor cannot be un-placed within the round).
//! * **strict round sequencing** — `StrictMonotonic` on `round_actions` (each action turn
//!   advances the counter).
//! * **the win** — the `score` method binds `winner == p ⇒ (charm_p >= 11 OR guilds_p >=
//!   4)` via `AnyOf[Not(FieldEquals(winner,p)), FieldGte(charm_p,11), FieldGte(guilds_p,4)]`,
//!   plus `WriteOnce(winner)` and `FieldGte(round_actions, 8)` (scoring only after the
//!   round completes). A false win claim is refused.
//!
//! `genesis` is the one permissive case (it seeds the initial counts + the heap keys the
//! relational teeth read as an `old` value).

use dregg_app_framework::{
    CellProgram, StateConstraint, TransitionCase, TransitionGuard, field_from_u64, symbol,
};
use dregg_cell::program::{HeapAtom, SimpleStateConstraint};
use dregg_schema::layout::{CheckedLayout, Slot, allocate_checked};
use dregg_schema::schema::Schema;
use dregg_schema::{genesis_oneshot_teeth, genesis_sentinel_freeze};
use spween_dregg::CompiledStory;

use crate::reference::{ActionKind, N_GUILDS, Player};

/// The scene id that fixes the deterministic world-cell identity.
pub const SCENE_ID: &str = "dregg-multiway-tug/phase0";
/// The permissive seeding method.
pub const GENESIS: &str = "genesis";
/// The scoring method.
pub const SCORE: &str = "score";

/// The 16 register components, in allocation order (slots `0..16`).
///
/// ⚠ APP-ROOT WELD — BLOCKED, diagnosis is a Lean-layout FACT (see docs/audit/CIRCUIT-LEAN-BOUNDARY.md).
/// `winner` rides slot 7 (was 12) so `octet_index_of_register(7) = 7 - FIELD_BASE(3) = 4` is a VALID
/// octet index — but the app-root weld (`PI[app] == octet[K]`) is UNSAT anyway, because the wide leg's
/// AFTER-block octet exposes the CELL'S committed `fields[0..8]`, and `winner` is an `.identity`
/// REGISTER-FILE component: it is absorbed into `state_commit`/`new8` but is NOT written into a
/// committed `fields[0..7]` lane, so octet lane 4 holds 0 while the winner is 2 (the driven `0 vs 2`
/// WitnessConflict). This slot move does NOT fix it (a register slot is not a cell field). THE REAL
/// FIX is a schema/lowering change: lower/mirror `winner` into a committed `fields[0..7]` lane — the
/// region the octet actually carries. Tracked as a tug follow-up; the fold test is `#[ignore]`d + red.
const REGISTERS: [&str; 16] = [
    "deck",
    "oop",
    "a_hand",
    "b_hand",
    "a_secret",
    "b_secret",
    "a_board",
    "winner",
    "a_charm",
    "b_charm",
    "a_guilds",
    "b_guilds",
    "b_board",
    "current",
    "round_actions",
    "scored",
];

fn player_tag(p: Player) -> &'static str {
    match p {
        Player::A => "a",
        Player::B => "b",
    }
}

fn action_tag(a: ActionKind) -> &'static str {
    match a {
        ActionKind::Secret => "secret",
        ActionKind::Discard => "discard",
        ActionKind::Gift => "gift",
        ActionKind::Competition => "comp",
    }
}

/// A used-flag component name for `(player, action)`.
pub fn flag_name(p: Player, a: ActionKind) -> String {
    format!("flag_{}_{}", player_tag(p), action_tag(a))
}

/// A per-guild placement-score component name for `(guild, player)`.
pub fn score_name(guild: usize, p: Player) -> String {
    format!("score_{}_{}", guild, player_tag(p))
}

/// Build the declared schema: 16 register components + 8 flag + 14 score collections.
pub fn schema() -> Schema {
    let mut s = Schema::new(SCENE_ID)
        .stat("deck", 0, 21)
        .stat("oop", 0, 21)
        .stat("a_hand", 0, 21)
        .stat("b_hand", 0, 21)
        .stat("a_secret", 0, 1)
        .stat("b_secret", 0, 1)
        .stat("a_board", 0, 21)
        // APP-ROOT WELD RELOCATION (the REAL slot assignment is this builder order, not the
        // REGISTERS[] array): `winner` rides slot 7 so `reg("winner")==7` lands inside the wide
        // leg's exposed fields[0..8] octet; `b_board` takes the vacated slot 12 (committed past the
        // octet via `fields_root`, sound for a by-name-resolved SumEquals conservation counter).
        .identity("winner")
        .stat("a_charm", 0, 21)
        .stat("b_charm", 0, 21)
        .stat("a_guilds", 0, 7)
        .stat("b_guilds", 0, 7)
        .stat("b_board", 0, 21)
        .stat("current", 0, 1)
        .stat("round_actions", 0, 8)
        .stat("scored", 0, 1);
    // Heap: used-flags then per-guild scores (heap keys 16.. in declaration order).
    for p in [Player::A, Player::B] {
        for a in [
            ActionKind::Secret,
            ActionKind::Discard,
            ActionKind::Gift,
            ActionKind::Competition,
        ] {
            s = s.collection(flag_name(p, a));
        }
    }
    for g in 0..N_GUILDS {
        for p in [Player::A, Player::B] {
            s = s.collection(score_name(g, p));
        }
    }
    s
}

/// The consumed, Legal-checked layout + the play-teeth program.
pub struct Deployment {
    pub layout: CheckedLayout,
}

impl Deployment {
    /// Allocate + Legal-check the schema (consuming dregg-schema's translation-validation
    /// allocator).
    pub fn new() -> Self {
        let layout = allocate_checked(&schema()).expect("multiway-tug layout is Legal");
        Deployment { layout }
    }

    /// Resolve a register component to its slot index.
    pub fn reg(&self, name: &str) -> u8 {
        match self.layout.resolve(name) {
            Some(Slot::Register(r)) => r,
            other => panic!("`{name}` is not a register: {other:?}"),
        }
    }

    /// Resolve a heap component to its key.
    pub fn key(&self, name: &str) -> u64 {
        match self.layout.resolve(name) {
            Some(Slot::Heap(k)) => k,
            other => panic!("`{name}` is not a heap key: {other:?}"),
        }
    }

    pub fn flag_key(&self, p: Player, a: ActionKind) -> u64 {
        self.key(&flag_name(p, a))
    }

    pub fn score_key(&self, guild: usize, p: Player) -> u64 {
        self.key(&score_name(guild, p))
    }

    /// The eight conservation-counter register indices summed by the `SumEquals` tooth.
    fn conservation_indices(&self) -> Vec<u8> {
        [
            "deck", "oop", "a_hand", "b_hand", "a_secret", "b_secret", "a_board", "b_board",
        ]
        .iter()
        .map(|n| self.reg(n))
        .collect()
    }

    /// The teeth shared by every non-genesis method: conservation + write-once flags +
    /// monotone scores.
    fn common_teeth(&self) -> Vec<StateConstraint> {
        let mut teeth = vec![StateConstraint::SumEquals {
            indices: self.conservation_indices(),
            value: field_from_u64(21),
        }];
        for p in [Player::A, Player::B] {
            for a in [
                ActionKind::Secret,
                ActionKind::Discard,
                ActionKind::Gift,
                ActionKind::Competition,
            ] {
                teeth.push(StateConstraint::HeapField {
                    key: self.flag_key(p, a),
                    atom: HeapAtom::WriteOnce,
                });
            }
        }
        for g in 0..N_GUILDS {
            for p in [Player::A, Player::B] {
                teeth.push(StateConstraint::HeapField {
                    key: self.score_key(g, p),
                    atom: HeapAtom::Monotonic,
                });
            }
        }
        // GENESIS ONE-SHOT (the write-hatch close, ported from the committed dregg-schema /
        // spween-dregg precedent): FREEZE the genesis-done sentinel on every non-genesis case.
        // `HeapField{Immutable}` admits the unchanged key (no play method ever writes it) but
        // REFUSES any write — so no stapled move can reset the sentinel to re-open the permissive
        // `constraints: vec![]` genesis case.
        teeth.push(genesis_sentinel_freeze());
        teeth
    }

    /// The `winner == who ⇒ (charm >= 11 OR guilds >= 4)` implication tooth.
    fn win_tooth(&self, who: u64, charm_reg: &str, guilds_reg: &str) -> StateConstraint {
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                    index: self.reg("winner"),
                    value: field_from_u64(who),
                })),
                SimpleStateConstraint::FieldGte {
                    index: self.reg(charm_reg),
                    value: field_from_u64(11),
                },
                SimpleStateConstraint::FieldGte {
                    index: self.reg(guilds_reg),
                    value: field_from_u64(4),
                },
            ],
        }
    }

    /// The hand-rolled play-teeth program.
    pub fn program(&self) -> CellProgram {
        let method_case = |name: &str, extra: Vec<StateConstraint>| {
            let mut constraints = self.common_teeth();
            constraints.extend(extra);
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol(name),
                },
                constraints,
            }
        };

        let round_actions = self.reg("round_actions");
        let action_extra = || {
            vec![StateConstraint::StrictMonotonic {
                index: round_actions,
            }]
        };

        let score_extra = vec![
            StateConstraint::FieldGte {
                index: round_actions,
                value: field_from_u64(8),
            },
            StateConstraint::WriteOnce {
                index: self.reg("winner"),
            },
            self.win_tooth(1, "a_charm", "a_guilds"),
            self.win_tooth(2, "b_charm", "b_guilds"),
        ];

        let cases = vec![
            // GENESIS: seeds counts + the heap keys the relational teeth read — but NO LONGER a
            // permissive `constraints: vec![]` write-hatch. It carries the ONE-SHOT teeth (the
            // `0 → 1` transition on `GENESIS_DONE_EXT_KEY`, `Equals{1} ∧ DeltaEquals{1}`):
            // admissible EXACTLY once (at deploy, sentinel still field-zero), jointly UNSAT for
            // every post-deploy genesis staple (`old == 1` forces `Δ == 0 ≠ 1`). The world births
            // the sentinel at deploy and injects the `0 → 1` write on the genesis method
            // (`WorldCell::commit`, keyed off this program carrying a `HeapField` over the
            // sentinel key — `program_requires_genesis_sentinel`).
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol(GENESIS),
                },
                constraints: genesis_oneshot_teeth(),
            },
            method_case(ActionKind::Secret.method(), action_extra()),
            method_case(ActionKind::Discard.method(), action_extra()),
            method_case(ActionKind::Gift.method(), action_extra()),
            method_case(ActionKind::Competition.method(), action_extra()),
            method_case(SCORE, score_extra),
        ];
        CellProgram::Cases(cases)
    }

    /// The compiled story to install on the world-cell.
    pub fn story(&self) -> CompiledStory {
        let mut var_slots = std::collections::BTreeMap::new();
        for name in REGISTERS {
            var_slots.insert(name.to_string(), self.reg(name) as usize);
        }
        CompiledStory {
            scene_id: SCENE_ID.to_string(),
            var_slots,
            has_slots: std::collections::BTreeMap::new(),
            passage_index: std::collections::BTreeMap::new(),
            program: self.program(),
            fully_gated: std::collections::BTreeMap::new(),
        }
    }
}

impl Default for Deployment {
    fn default() -> Self {
        Self::new()
    }
}
