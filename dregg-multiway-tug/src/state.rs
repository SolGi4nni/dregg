//! # The state declaration + the Lean-sourced play teeth.
//!
//! The multiway-tug STATE is declared as a [`dregg_schema::Schema`] and lowered by the
//! CONSUMED dregg-schema allocator ([`dregg_schema::layout::allocate_checked`]) to a
//! Legal (disjoint + in-bounds, the RotatedLayout discipline) slot/heap layout: the 16
//! scalar counters/win-registers land in the register file, the 8 used-flags + 14
//! per-guild placement scores land on heap keys `16..37`.
//!
//! The PLAY TEETH are **authored in Lean** (`metatheory/Dregg2/Games/MultiwayTugProgram.lean
//! :: multiwayTugProgram`), emitted to `program/multiway_tug_program.json`, and LOADED by
//! [`Deployment::program`] via [`crate::program_loader`], which resolves the symbolic slot/method
//! NAMES against this allocator. There is no hand-rolled `CellProgram::Cases` in Rust — the
//! deployed program IS the Lean object (see `docs/audit/SEMANTIC-LEAN-BOUNDARY.md` Step 1 / T4).
//! The teeth the Lean value encodes, each still exactly the deployed referee:
//!
//! * **21-card conservation** — `SumEquals` over the eight card-zone counters `== 21`, on
//!   EVERY move post-state. A play that conjures or destroys a favor breaks the sum and is
//!   refused.
//! * **one-action-per-round** — `HeapAtom::WriteOnce` on each `(player, action)` used-flag
//!   (written with the round's strictly-increasing action stamp, so any reuse changes the
//!   frozen flag and is refused).
//! * **monotone scores** — `HeapAtom::Monotonic` on each per-guild placement counter (a
//!   placed favor cannot be un-placed within the round).
//! * **strict round sequencing** — `StrictMonotonic` on `round_actions` (each committed turn
//!   advances the counter; a full round is 8 actions + 4 responses = 12).
//!
//! * **the escrow interlock** — the `pending_kind` heap key. `gift`/`comp` bind it
//!   `Equals{1}/{2} ∧ DeltaEquals{+1}/{+2}`; the two PRIVATE actions and `score` bind it
//!   `Equals{0} ∧ DeltaEquals{0}`; and only `respond_gift`/`respond_comp` may take it back
//!   down (`DeltaEquals{-1}/{-2}`). So a seat cannot walk away from a standing offer, and the
//!   marker cannot be cleared except by answering the offer that raised it.
//! * **the win** — ⚑ the deployed gate is the model's TERMINAL RULE `roundWinner`, not the
//!   absolute bar `Won`. Each of the rule's nine clauses is its own transition case
//!   (`score_charm_a` … `score_draw`, see [`score_method`]), carrying that clause's guard —
//!   thresholds as `FieldGte` / `AnyOf[Not(FieldGte)]`, leads as the cross-register
//!   `FieldLteOther` — conjoined with `winner == w` for the seat that clause names, plus
//!   `WriteOnce(winner)` and `FieldGte(round_actions, 12)`. The clauses partition, so exactly one
//!   case can admit a scored state and it is the one the proven rule selects
//!   (`scoreBranchTeeth_admits_iff_branch`). A false win claim, and a false CLAUSE, are refused.
//!
//! `genesis` is the one permissive case (it seeds the initial counts + the heap keys the
//! relational teeth read as an `old` value).

use dregg_app_framework::CellProgram;
use dregg_schema::layout::{CheckedLayout, Slot, allocate_checked};
use dregg_schema::schema::Schema;
use spween_dregg::CompiledStory;

use crate::reference::{ActionKind, N_GUILDS, Player};

/// The scene id that fixes the deterministic world-cell identity.
pub const SCENE_ID: &str = "dregg-multiway-tug/phase0";
/// The permissive seeding method.
pub const GENESIS: &str = "genesis";

/// **The deployed method a scoring turn commits under, for clause `branch` of the terminal rule.**
///
/// ⚑ There is no single `score` method any more, and that is the repair rather than a refactor.
/// The terminal rule is `roundWinner`, a PRECEDENCE of nine clauses (absolute charm bar, absolute
/// row bar, then charm lead, then row lead at equal charm, then an exact dead heat). Its tail
/// compares REGISTER TO REGISTER, and the deployed alphabet carries such a comparison only at top
/// level (`StateConstraint::FieldLteOther`) — never inside `AnyOf`, whose `SimpleStateConstraint`
/// variants are all register-vs-literal. Top-level constraints in a case conjoin, so a disjunction
/// over cross-register tests cannot live in one case at all. `CellProgram::Cases` dispatches on the
/// method name, so the disjunction BECOMES the method: one case per clause, each carrying that
/// clause's guard and the `winner` value it names.
///
/// The clause comes from the Lean oracle ([`crate::rules::adjudicate`]) and the NAME comes from the
/// Lean-emitted artifact ([`crate::program_loader::score_branch_method`]). Rust holds neither.
pub fn score_method(branch: u8) -> String {
    crate::program_loader::score_branch_method(branch)
}

/// The 16 register components, in allocation order (slots `0..16`).
///
/// APP-ROOT WELD — RESOLVED. `winner` rides slot 7 (was 12) so it lands inside the wide leg's exposed
/// AFTER-block `fields[0..8]` octet — the region with direct lane-0 limbs (`fields[8..16]` ride only
/// the opaque `fields_root`/authority digest and CANNOT be app-root exposed). A schema `Slot::Register(r)`
/// IS the cell's committed `fields[r]` (the game writes `winner` via `SetField{index: reg("winner")=7}`
/// -> `cell.state.fields[7]`; `.identity` vs `.stat` only picks the tooth, not the commitment location),
/// and the producer puts `fields[k]` at octet index `k`. So `winner` IS committed at octet index 7, and
/// the fold welds it with `field_key = reg("winner")` (see `fold::mint_win_turn_over_cell`). The earlier
/// `0 vs 2` conflict was a WRONG octet-index map (`octet_index_of_register(7) = 4` aimed the weld at
/// `a_secret`), NOT a missing commitment — fixed by using the cell field slot directly.
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
        // The turn stamp counts ACTIONS AND RESPONSES: a full round is 8 actions + 4
        // responses = 12 (the Lean `#guard (8 + 4 : ℕ) = 12`).
        .stat("round_actions", 0, 12)
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
    // ⚑ THE OFFER ON THE TABLE (0 none, 1 gift, 2 competition). Declared LAST, after the 8
    // flag and 14 score collections, so every existing heap key assignment stays put.
    s = s.collection(PENDING_KIND);
    s
}

/// The heap component naming the offer currently on the table.
pub const PENDING_KIND: &str = "pending_kind";

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

    /// The heap key carrying the pending-offer marker (0 none, 1 gift, 2 competition).
    pub fn pending_kind_key(&self) -> u64 {
        self.key(PENDING_KIND)
    }

    /// The play-teeth program, **LOADED from the Lean source of truth**.
    ///
    /// The teeth are authored in Lean
    /// (`metatheory/Dregg2/Games/MultiwayTugProgram.lean :: multiwayTugProgram`) and emitted to
    /// `program/multiway_tug_program.json`; [`crate::program_loader::load_program`] deserializes
    /// that artifact and resolves the symbolic slot/method names against this allocator. There is
    /// no hand-rolled `CellProgram::Cases` in Rust anymore — the deployed program IS the Lean
    /// object (edit a threshold in the Lean source, re-emit via `program/regen.sh`, and the
    /// deployed game changes). See `docs/audit/SEMANTIC-LEAN-BOUNDARY.md` Step 1 / T4.
    pub fn program(&self) -> CellProgram {
        crate::program_loader::load_program(self)
    }

    /// The compiled story to install on the world-cell.
    pub fn story(&self) -> CompiledStory {
        let mut var_slots = std::collections::BTreeMap::new();
        for name in REGISTERS {
            var_slots.insert(name.to_string(), self.reg(name) as u64);
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
