//! # `combat` — a turn-based TACTICAL combat engine on the REAL dregg substrate
//!
//! Where [`crate::dice_combat`] binds ONE verifiable die roll into ONE trade-blows
//! turn, this module is the original ambition's centerpiece: a full **turn-based
//! tactical battle** — a party of heroes against a group of enemies — played out as
//! a chain of real cap-bounded [`TurnReceipt`]s on `spween-dregg`'s real
//! [`WorldCell`], every rule an executor-enforced [`StateConstraint`] tooth the
//! verified `EmbeddedExecutor` re-checks. Nothing here is a host `if`: the legality
//! of every ability is a kernel predicate, and an illegal move is a REAL
//! [`WorldError::Refused`] that commits nothing (anti-ghost).
//!
//! ## The battle is ONE cell (combatants / initiative / status as cell state)
//!
//! The whole fight lives in a single dregg cell. Its 16 register slots hold the hot
//! control + per-combatant flag state; its committed heap (`fields_map`, keys ≥ 16)
//! holds the per-combatant scalars, so the engine scales past the register budget
//! exactly as the keep's inventory does.
//!
//! | state | where | role |
//! |-------|-------|------|
//! | `active` | register | whose turn it is (the initiative pointer) |
//! | `focus_spent` / `focus_budget` | registers | the party's shared special-move resource |
//! | `dn{c}` | register (per combatant) | DOWNED flag — a defeated combatant |
//! | `gd{c}` | register (per combatant) | GUARDING status |
//! | `st{c}` | register (per combatant) | STUNNED status |
//! | `hp[c]` | heap key `100+c` | hit points |
//! | `poison[c]` | heap key `200+c` | poison stacks |
//! | `heavy_round[c]` | heap key `400+c` | the round of the last heavy strike (cooldown) |
//!
//! ## The abilities, and the executor tooth each is gated by
//!
//! Every ability is dispatched as a distinct cell method, and the compiler-shaped
//! [`CellProgram`] is default-deny: a method matching no installed case is a real
//! [`ProgramError::NoTransitionCaseMatched`] refusal. Each case carries the real teeth:
//!
//! - **attack** (a basic blow) — a real [`dregg_dice`] `d8` draw, bound into the
//!   receipt via `EmitEvent` and REPRODUCED on replay ([`reverify_draw`]). Teeth:
//!   `AllowedTransitions(active)` (act only on your turn), `UntilEvent(st{a})` (a
//!   stunned actor cannot strike), `UntilEvent(dn{a})` / `UntilEvent(dn{t})` (a downed
//!   combatant cannot act, a downed target cannot be attacked), and the HP FLOOR
//!   `HeapField(hp[t], Gte 1)` — a blow that would drop the target below 1 is REFUSED
//!   (an overkill cannot underflow the ledger).
//! - **guard** — sets `gd{a}`, a real status the teeth respect: incoming damage is
//!   reduced, and a guarding target cannot be executed (see finish).
//! - **heavy** (the special/heavy strike — heroes only) — a higher-variance `d12`
//!   draw + POISON + STUN applied to the target. Teeth add the RESOURCE cost
//!   `FieldLteField(focus_spent, focus_budget)` (an overspend is refused) and the
//!   COOLDOWN `HeapField(heavy_round[a], StrictMonotonic)` (at most once per round —
//!   the recorded round must strictly increase).
//! - **finish** (the execute) — how a combatant is defeated. Teeth: the target must be
//!   WEAKENED (`HeapField(hp[t], Lte FINISH_THRESHOLD)` — a healthy target cannot be
//!   executed), NOT already downed (`UntilEvent(dn{t})`), NOT guarding
//!   (`UntilEvent(gd{t})`), and the down is WRITE-ONCE (`WriteOnce(dn{t})`).
//! - **pass** — a stunned/held combatant yields its turn (clearing its own stun).
//! - **tick** — a round-start poison tick, floored by the same `HeapField(hp, Gte 1)`.
//!
//! ## Initiative, rounds, resolution
//!
//! Turn order is DICE-ROLLED: each combatant rolls a verifiable `d20` initiative
//! ([`initiative_order`], a pure reproducible function of the arena seed), sorted
//! high-to-low. The driver sequences whose turn is next in that order (skipping the
//! downed); the executor enforces the *invariant* — only the combatant the `active`
//! pointer names may act. A round is one full pass; the fight resolves to
//! [`Outcome::Victory`] (all enemies downed) or [`Outcome::Defeat`] (all heroes
//! downed). Each committed turn chains onto the last (`pre == prev.post`).
//!
//! ## Honest scope
//!
//! - **Single-cell combat state.** The whole party+enemy state is one cell (one serial
//!   writer). A truly concurrent multi-party battle (each hero its own cell/identity
//!   acting simultaneously) is the multi-cell frontier — see [`crate::multicell`] /
//!   [`crate::mud`]; it is not claimed here.
//! - **Reproducible, not unpredictable dice.** As in [`crate::dice_combat`], the draws
//!   use the `Deterministic` source: they REPRODUCE exactly on replay (which is what the
//!   receipt binding + [`reverify_draw`] demonstrate). The non-grindable `ServerVrf` /
//!   `Hybrid` sources are the named `dregg-dice` follow-up.
//! - **The balance numbers are design params.** Die sizes, HP, focus cost, the finish
//!   threshold — all tunable. What the teeth *guarantee* are the LEDGER INVARIANTS: no
//!   HP underflow, no acting out of turn, no attacking the dead, no overspending the
//!   resource, one execute per target, the cooldown, and a reproduced (un-forgeable)
//!   damage roll.
//!
//! [`TurnReceipt`]: dregg_app_framework::TurnReceipt
//! [`StateConstraint`]: dregg_app_framework::StateConstraint
//! [`CellProgram`]: dregg_app_framework::CellProgram
//! [`ProgramError::NoTransitionCaseMatched`]: dregg_cell::program::ProgramError

use std::sync::Arc;

use dregg_app_framework::{
    CellId, CellProgram, Effect, Event, FieldElement, StateConstraint, TransitionCase,
    TransitionGuard, TurnReceipt, field_from_u64, symbol,
};
use dregg_cell::program::HeapAtom;
use dregg_dice::source::Deterministic;
use dregg_dice::{
    DrawError, DrawStream, RandomnessEvidence, RandomnessRequest, RandomnessSource, VerifyError,
};
use spween_dregg::{
    CompiledStory, Value, WorldCell, WorldError, compile_scene, field_to_u64, parse,
};

// ── Roster ───────────────────────────────────────────────────────────────────

/// The number of combatants in the arena (2 heroes + 2 enemies).
pub const N: u8 = 4;

/// Hero 0 — the Ranger.
pub const RANGER: u8 = 0;
/// Hero 1 — the Cleric.
pub const CLERIC: u8 = 1;
/// Enemy 0 — the gate-Warden.
pub const WARDEN: u8 = 2;
/// Enemy 1 — the Hound.
pub const HOUND: u8 = 3;

/// Combatants `0..2` are heroes; `2..4` are enemies.
pub fn is_hero(c: u8) -> bool {
    c < 2
}

/// The display name of a combatant.
pub fn name(c: u8) -> &'static str {
    ["Ranger", "Cleric", "Warden", "Hound"][c as usize]
}

/// The living-or-dead combatants on the opposite team from `c`.
pub fn opponents(c: u8) -> Vec<u8> {
    (0..N).filter(|&x| is_hero(x) != is_hero(c)).collect()
}

// ── Design parameters (the balance numbers — the teeth guarantee the invariants) ─

/// The basic attack die (`d8`).
pub const ATTACK_DIE: u64 = 8;
/// The heavy/special die (`d12`, higher variance).
pub const HEAVY_DIE: u64 = 12;
/// The initiative die (`d20`).
pub const INITIATIVE_DIE: u64 = 20;
/// A target at or below this HP can be EXECUTED (the finish move). A healthy target
/// (above it) cannot — the `HeapField(hp, Lte)` tooth refuses.
pub const FINISH_THRESHOLD: u64 = 8;
/// The focus a heavy strike costs (drawn from the shared party budget).
pub const HEAVY_FOCUS_COST: u64 = 15;
/// The shared party focus budget (`FieldLteField` cross-slot bound).
pub const FOCUS_BUDGET: u64 = 40;
/// Poison stacks a heavy strike inflicts.
pub const HEAVY_POISON: u64 = 3;
/// Flat damage reduction a guarding combatant enjoys (floored so a blow deals ≥ 1).
pub const GUARD_REDUCTION: u64 = 3;
/// Default starting HP for a hero.
pub const HERO_HP: u64 = 26;
/// Default starting HP for an enemy.
pub const ENEMY_HP: u64 = 16;

// ── Heap key scheme (keys ≥ 16 route into the committed `fields_map`) ────────────

const HP_BASE: u64 = 100;
const POISON_BASE: u64 = 200;
const HEAVY_ROUND_BASE: u64 = 400;

/// The heap key holding combatant `c`'s hit points.
pub fn hp_key(c: u8) -> u64 {
    HP_BASE + c as u64
}
/// The heap key holding combatant `c`'s poison stacks.
pub fn poison_key(c: u8) -> u64 {
    POISON_BASE + c as u64
}
/// The heap key holding the round of combatant `c`'s last heavy strike (cooldown).
pub fn heavy_round_key(c: u8) -> u64 {
    HEAVY_ROUND_BASE + c as u64
}

// ── Register var names (the compiler assigns each a slot) ────────────────────────

const V_ACTIVE: &str = "active";
const V_FSPENT: &str = "focus_spent";
const V_FBUDGET: &str = "focus_budget";

fn dn_name(c: u8) -> String {
    format!("dn{c}")
}
fn gd_name(c: u8) -> String {
    format!("gd{c}")
}
fn st_name(c: u8) -> String {
    format!("st{c}")
}

// ── Method names (each an installed `CellProgram` case — default-deny) ───────────

const M_SETUP: &str = "setup";
fn m_attack(a: u8, t: u8) -> String {
    format!("atk/{a}/{t}")
}
fn m_heavy(a: u8, t: u8) -> String {
    format!("hvy/{a}/{t}")
}
fn m_finish(a: u8, t: u8) -> String {
    format!("fin/{a}/{t}")
}
fn m_guard(c: u8) -> String {
    format!("grd/{c}")
}
fn m_pass(c: u8) -> String {
    format!("pas/{c}")
}
fn m_tick(c: u8) -> String {
    format!("tick/{c}")
}

// ── Dice binding (mirrors `dice_combat`, generalized to attacker/target/ability) ─

/// The topic a combat draw's binding rides on the real receipt (distinct from the
/// single-blow [`crate::dice_combat::DICE_TOPIC`] and any state method).
pub const DICE_TOPIC: &str = "dungeon-on-dregg/tactical-combat/dice-draw-v1";
/// The purpose tag domain-separating combat-hit draws.
pub const COMBAT_EVENT_KIND: &str = "combat/hit";
/// The purpose tag domain-separating initiative draws.
pub const INITIATIVE_EVENT_KIND: &str = "combat/initiative";
/// The committed game identity folded into every request's `game_binding`.
const GAME_BINDING: &[u8] = b"dungeon-on-dregg/tactical-combat/v1";

/// Which dice-driven ability a draw resolved (bound into its `action_hash`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ability {
    /// A basic attack (`d8`).
    Attack,
    /// A heavy/special strike (`d12` + poison + stun).
    Heavy,
}

impl Ability {
    fn tag(self) -> u8 {
        match self {
            Ability::Attack => 0,
            Ability::Heavy => 1,
        }
    }
    fn die(self) -> u64 {
        match self {
            Ability::Attack => ATTACK_DIE,
            Ability::Heavy => HEAVY_DIE,
        }
    }
}

/// The damage a die face inflicts, given the target's guard status: a guarding target
/// takes a flat reduction (floored so every landed blow deals ≥ 1). Factored out so
/// [`reverify_draw`] and the resolve path agree on the rule.
pub fn damage_of_roll(roll: u64, guarded: bool) -> u64 {
    if guarded {
        roll.saturating_sub(GUARD_REDUCTION).max(1)
    } else {
        roll
    }
}

/// A deterministic (reproducible) context for the [`Deterministic`] source.
fn combat_context(req: &RandomnessRequest) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/tactical-combat/context/v1");
    h.update(req.event_id().as_bytes());
    *h.finalize().as_bytes()
}

/// Hash the world-cell's committed control state + every combatant's HP into the
/// pre-state root bound into a combat draw's `EventId`.
fn pre_state_root(world: &WorldCell) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/tactical-combat/pre-state/v1");
    for slot in world.snapshot() {
        h.update(&slot.to_le_bytes());
    }
    for c in 0..N {
        h.update(&world.read_heap(hp_key(c)).unwrap_or(0).to_le_bytes());
    }
    *h.finalize().as_bytes()
}

/// A commitment to the finalized combat action (attacker, target, ability, die).
fn action_hash(a: u8, t: u8, ability: Ability, sides: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/tactical-combat/action/v1");
    h.update(&[a, t, ability.tag()]);
    h.update(&sides.to_le_bytes());
    *h.finalize().as_bytes()
}

/// Build the [`RandomnessRequest`] for a `(seq, attacker, target, ability)` draw.
fn combat_request(
    world: &WorldCell,
    seq: u64,
    a: u8,
    t: u8,
    ability: Ability,
) -> RandomnessRequest {
    RandomnessRequest {
        game_binding: GAME_BINDING.to_vec(),
        seq,
        pre_state_root: pre_state_root(world),
        action_hash: action_hash(a, t, ability, ability.die()),
        event_kind: COMBAT_EVENT_KIND.to_string(),
        draw_count: 1,
    }
}

/// Produce evidence + a verified seed for `req` and read the die face off the stream.
fn roll_request(req: &RandomnessRequest, sides: u64) -> (u64, RandomnessEvidence) {
    let source = Deterministic {
        context: combat_context(req),
    };
    let evidence = source.evidence(req);
    let seed =
        Deterministic::seed(req, &evidence).expect("freshly-produced combat evidence verifies");
    let roll = DrawStream::new(seed, req.draw_count)
        .draw_die(0, sides)
        .expect("draw_count = 1, so index 0 is in range");
    (roll, evidence)
}

/// A resolved combat draw carried alongside the receipt so [`reverify_draw`] can
/// re-derive and check it.
#[derive(Clone, Debug)]
pub struct CombatDraw {
    /// The randomness request binding the turn context (its `EventId` seeds the draw).
    pub request: RandomnessRequest,
    /// The recorded evidence a verifier re-derives the seed from.
    pub evidence: RandomnessEvidence,
    /// The die face rolled (`1..=sides`).
    pub roll: u64,
    /// The damage applied to the target's HP (roll, minus guard mitigation).
    pub damage: u64,
    /// Whether the target was guarding when the blow landed (fixes the damage rule).
    pub guarded: bool,
    /// The die used.
    pub sides: u64,
    /// The attacker.
    pub attacker: u8,
    /// The target.
    pub target: u8,
    /// The ability the draw resolved.
    pub ability: Ability,
}

/// The five fields bound into a combat receipt's `EmitEvent`, read back exactly as a
/// stranger replaying the chain would.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundDraw {
    /// The draw's `EventId` bytes (`data[0]`).
    pub event_id: FieldElement,
    /// The draw-transcript commitment (`data[1]`).
    pub transcript: FieldElement,
    /// The die face bound into the turn (`data[2]`).
    pub roll: u64,
    /// The damage bound into the turn (`data[3]`).
    pub damage: u64,
    /// The guard flag bound into the turn (`data[4]`, fixes the damage rule).
    pub guarded: bool,
}

/// The `EmitEvent` that binds a combat draw into the turn.
fn dice_event_effect(cell: CellId, draw: &CombatDraw) -> Effect {
    let data = vec![
        *draw.request.event_id().as_bytes(),
        draw.evidence.draw_transcript_commitment,
        field_from_u64(draw.roll),
        field_from_u64(draw.damage),
        field_from_u64(draw.guarded as u64),
    ];
    Effect::EmitEvent {
        cell,
        event: Event::new(symbol(DICE_TOPIC), data),
    }
}

/// Read the bound combat draw off a committed receipt (the stranger's replay path).
pub fn bound_draw(receipt: &TurnReceipt) -> Option<BoundDraw> {
    let topic = symbol(DICE_TOPIC);
    let e = receipt.emitted_events.iter().find(|e| e.topic == topic)?;
    if e.data.len() < 5 {
        return None;
    }
    Some(BoundDraw {
        event_id: e.data[0],
        transcript: e.data[1],
        roll: field_to_u64(&e.data[2]),
        damage: field_to_u64(&e.data[3]),
        guarded: field_to_u64(&e.data[4]) != 0,
    })
}

/// Why re-verifying a bound combat draw failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiceReplayError {
    /// The receipt bound no dice event under [`DICE_TOPIC`].
    NoBinding,
    /// The recorded evidence did not verify against the recorded request.
    Evidence(VerifyError),
    /// Re-deriving the draw from the verified seed failed.
    Draw(DrawError),
    /// The `EventId` bound into the receipt is not the recorded request's.
    EventIdMismatch,
    /// The transcript commitment bound into the receipt is not the recorded evidence's.
    TranscriptMismatch,
    /// The roll bound into the receipt is not the one re-derived — a FORGED roll.
    RollMismatch {
        /// The value bound into the receipt.
        bound: u64,
        /// The value re-derived from the recorded request + evidence.
        rederived: u64,
    },
    /// The guard flag bound into the receipt is not the recorded one (a retcon of the
    /// mitigation context that fixes the damage rule).
    GuardMismatch {
        /// The flag bound into the receipt.
        bound: bool,
        /// The flag the recorded draw carried.
        recorded: bool,
    },
    /// The damage bound into the receipt is not the function of the roll (+ guard) the
    /// rules fix — a forged damage.
    DamageMismatch {
        /// The damage bound into the receipt.
        bound: u64,
        /// The damage the roll + guard flag fix.
        expected: u64,
    },
}

impl std::fmt::Display for DiceReplayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DiceReplayError::NoBinding => write!(f, "the receipt bound no dice draw"),
            DiceReplayError::Evidence(e) => write!(f, "the dice evidence did not verify: {e:?}"),
            DiceReplayError::Draw(e) => write!(f, "re-deriving the draw failed: {e:?}"),
            DiceReplayError::EventIdMismatch => {
                write!(f, "the bound EventId is not the recorded request's")
            }
            DiceReplayError::TranscriptMismatch => {
                write!(f, "the bound transcript is not the recorded evidence's")
            }
            DiceReplayError::RollMismatch { bound, rederived } => write!(
                f,
                "forged roll: the receipt binds {bound} but the seed re-derives {rederived}"
            ),
            DiceReplayError::GuardMismatch { bound, recorded } => write!(
                f,
                "forged guard context: the receipt binds {bound} but the record carries {recorded}"
            ),
            DiceReplayError::DamageMismatch { bound, expected } => write!(
                f,
                "forged damage: the receipt binds {bound} but the roll fixes {expected}"
            ),
        }
    }
}

impl std::error::Error for DiceReplayError {}

/// **The replay tooth.** Re-derive the seed from the RECORDED `(request, evidence)`
/// through `dregg-dice`'s pure verifier, re-derive the draw, and confirm the roll +
/// damage BOUND into the real receipt match. A forged (gentler) roll or damage is
/// caught. Returns the re-derived roll on success.
pub fn reverify_draw(receipt: &TurnReceipt, draw: &CombatDraw) -> Result<u64, DiceReplayError> {
    let seed =
        Deterministic::seed(&draw.request, &draw.evidence).map_err(DiceReplayError::Evidence)?;
    let rederived = DrawStream::new(seed, draw.request.draw_count)
        .draw_die(0, draw.sides)
        .map_err(DiceReplayError::Draw)?;
    let bound = bound_draw(receipt).ok_or(DiceReplayError::NoBinding)?;
    if bound.event_id != *draw.request.event_id().as_bytes() {
        return Err(DiceReplayError::EventIdMismatch);
    }
    if bound.transcript != draw.evidence.draw_transcript_commitment {
        return Err(DiceReplayError::TranscriptMismatch);
    }
    if bound.roll != rederived {
        return Err(DiceReplayError::RollMismatch {
            bound: bound.roll,
            rederived,
        });
    }
    if bound.guarded != draw.guarded {
        return Err(DiceReplayError::GuardMismatch {
            bound: bound.guarded,
            recorded: draw.guarded,
        });
    }
    let expected = damage_of_roll(rederived, bound.guarded);
    if bound.damage != expected {
        return Err(DiceReplayError::DamageMismatch {
            bound: bound.damage,
            expected,
        });
    }
    Ok(rederived)
}

// ── Initiative (dice-rolled, reproducible) ──────────────────────────────────────

fn initiative_request(seed: u8, c: u8) -> RandomnessRequest {
    let mut ph = blake3::Hasher::new();
    ph.update(b"dungeon-on-dregg/tactical-combat/initiative/pre-state/v1");
    ph.update(&[seed]);
    let mut ah = blake3::Hasher::new();
    ah.update(b"dungeon-on-dregg/tactical-combat/initiative/action/v1");
    ah.update(&[c]);
    RandomnessRequest {
        game_binding: GAME_BINDING.to_vec(),
        seq: c as u64,
        pre_state_root: *ph.finalize().as_bytes(),
        action_hash: *ah.finalize().as_bytes(),
        event_kind: INITIATIVE_EVENT_KIND.to_string(),
        draw_count: 1,
    }
}

/// The initiative roll (a verifiable `d20`) for each combatant — a pure, reproducible
/// function of the arena seed.
pub fn initiative_rolls(seed: u8) -> Vec<(u8, u64)> {
    (0..N)
        .map(|c| {
            (
                c,
                roll_request(&initiative_request(seed, c), INITIATIVE_DIE).0,
            )
        })
        .collect()
}

/// The initiative ORDER: combatants sorted by roll (high first), ties broken by id.
pub fn initiative_order(seed: u8) -> Vec<u8> {
    let mut r = initiative_rolls(seed);
    r.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    r.into_iter().map(|(c, _)| c).collect()
}

// ── The installed program (every ability a case with real teeth) ────────────────

fn slot(story: &CompiledStory, name: &str) -> u8 {
    (*story
        .var_slots
        .get(name)
        .unwrap_or_else(|| panic!("combat var `{name}` has a compiled slot"))) as u8
}

/// The turn-order tooth for combatant `a`: `active` may only transition FROM `a`
/// (i.e. it must be `a`'s turn). Any handoff target is allowed (the driver sequences
/// the next living combatant); the invariant enforced is "act only on your turn".
fn handoff(a: u8, active_slot: u8) -> StateConstraint {
    let allowed = (0..N)
        .map(|x| (field_from_u64(a as u64), field_from_u64(x as u64)))
        .collect();
    StateConstraint::AllowedTransitions {
        slot_index: active_slot,
        allowed,
    }
}

fn hp_floor(t: u8) -> StateConstraint {
    StateConstraint::HeapField {
        key: hp_key(t),
        atom: HeapAtom::Gte {
            value: field_from_u64(1),
        },
    }
}

/// Build the full combat [`CellProgram`] — one method-guarded case per ability per
/// (attacker, target), each carrying the executor-enforced teeth.
fn build_program(story: &CompiledStory) -> CellProgram {
    let active = slot(story, V_ACTIVE);
    let fspent = slot(story, V_FSPENT);
    let fbudget = slot(story, V_FBUDGET);
    let dn = |c: u8| slot(story, &dn_name(c));
    let gd = |c: u8| slot(story, &gd_name(c));
    let st = |c: u8| slot(story, &st_name(c));

    let case = |method: &str, constraints: Vec<StateConstraint>| TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(method),
        },
        constraints,
    };

    let mut cases = vec![case(M_SETUP, vec![])];

    for a in 0..N {
        cases.push(case(&m_guard(a), vec![handoff(a, active)]));
        cases.push(case(&m_pass(a), vec![handoff(a, active)]));
        cases.push(case(&m_tick(a), vec![hp_floor(a)]));

        for &t in &opponents(a) {
            // basic attack
            cases.push(case(
                &m_attack(a, t),
                vec![
                    handoff(a, active),
                    StateConstraint::UntilEvent { flag_index: st(a) },
                    StateConstraint::UntilEvent { flag_index: dn(a) },
                    StateConstraint::UntilEvent { flag_index: dn(t) },
                    hp_floor(t),
                ],
            ));
            // heavy/special (heroes only)
            if is_hero(a) {
                cases.push(case(
                    &m_heavy(a, t),
                    vec![
                        handoff(a, active),
                        StateConstraint::UntilEvent { flag_index: st(a) },
                        StateConstraint::UntilEvent { flag_index: dn(a) },
                        StateConstraint::UntilEvent { flag_index: dn(t) },
                        hp_floor(t),
                        StateConstraint::FieldLteField {
                            left_index: fspent,
                            right_index: fbudget,
                        },
                        StateConstraint::HeapField {
                            key: heavy_round_key(a),
                            atom: HeapAtom::StrictMonotonic,
                        },
                    ],
                ));
            }
            // finish / execute
            cases.push(case(
                &m_finish(a, t),
                vec![
                    handoff(a, active),
                    StateConstraint::UntilEvent { flag_index: st(a) },
                    StateConstraint::UntilEvent { flag_index: dn(a) },
                    StateConstraint::UntilEvent { flag_index: dn(t) },
                    StateConstraint::UntilEvent { flag_index: gd(t) },
                    StateConstraint::HeapField {
                        key: hp_key(t),
                        atom: HeapAtom::Lte {
                            value: field_from_u64(FINISH_THRESHOLD),
                        },
                    },
                    StateConstraint::WriteOnce { index: dn(t) },
                ],
            ));
        }
    }

    CellProgram::Cases(cases)
}

/// The combat scene: one passage naming every register var (so the compiler assigns
/// each a slot). The program is then REPLACED with [`build_program`]; the scene's own
/// trivial choice is unused.
fn combat_dsl() -> String {
    let mut s = String::from(
        "---\nid: tactical-arena\ntitle: The Tactical Arena\nweight: 1\n---\n\n=== arena\n\n",
    );
    s.push_str(&format!(
        "~ {V_ACTIVE} = 0\n~ {V_FSPENT} = 0\n~ {V_FBUDGET} = 0\n"
    ));
    for c in 0..N {
        s.push_str(&format!("~ {} = 0\n", dn_name(c)));
        s.push_str(&format!("~ {} = 0\n", gd_name(c)));
        s.push_str(&format!("~ {} = 0\n", st_name(c)));
    }
    s.push_str("\nThe arena hushes as steel is drawn.\n\n* [Begin the battle]\n  -> END\n");
    s
}

/// Compile the combat scene and install the tactical program.
pub fn combat_compiled() -> CompiledStory {
    let scene = parse(&combat_dsl(), "tactical-arena.scene").expect("the combat scene parses");
    let mut story = compile_scene(&scene).expect("the combat scene compiles");
    story.program = build_program(&story);
    story
}

// ── The arena (the living battle) ───────────────────────────────────────────────

/// The resolution of a battle.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Outcome {
    /// The fight is not over.
    Ongoing,
    /// Every enemy is downed.
    Victory,
    /// Every hero is downed.
    Defeat,
}

/// A landed blow: the real receipt, the draw its damage came from, and the target's HP
/// after.
#[derive(Clone, Debug)]
pub struct Hit {
    /// The committed turn receipt (its `effects_hash`/`turn_hash` bind the draw).
    pub receipt: TurnReceipt,
    /// The draw the damage was resolved from.
    pub draw: CombatDraw,
    /// The target's committed HP after the blow.
    pub target_hp_after: u64,
}

/// One recorded action of a fight (for the example to print / the test to assert).
#[derive(Clone, Debug)]
pub struct FightEvent {
    /// The round the action fell in.
    pub round: u64,
    /// The acting combatant.
    pub actor: u8,
    /// The kind of action (`"attack"`, `"heavy"`, `"finish"`, `"guard"`, `"pass"`, `"tick"`).
    pub kind: &'static str,
    /// The target, if any.
    pub target: Option<u8>,
    /// The die roll, for dice-driven actions.
    pub roll: Option<u64>,
    /// The damage dealt, for dice-driven actions.
    pub damage: Option<u64>,
    /// The committed turn hash.
    pub turn_hash: [u8; 32],
    /// A human note.
    pub note: String,
}

/// The living tactical battle: the real world-cell + the driver-side bookkeeping the
/// executor cannot compute for itself (the initiative order, the round counter, the
/// action sequence). Every mutating method lands a real turn (or a real refusal).
pub struct Arena {
    /// The real world-cell hosting the whole battle.
    pub world: WorldCell,
    story: Arc<CompiledStory>,
    /// The dice-rolled initiative order (all combatants, downed skipped when advancing).
    pub order: Vec<u8>,
    /// The recorded initiative rolls.
    pub inits: Vec<(u8, u64)>,
    /// The current round (starts at 1; the heavy cooldown is once per round).
    pub round: u64,
    /// The global action sequence (each dice draw binds it).
    pub seq: u64,
    /// The setup turn's receipt — the root the combat receipt chain links onto.
    pub genesis: TurnReceipt,
    active: u8,
    fspent: u8,
    dn: [u8; 4],
    gd: [u8; 4],
    st: [u8; 4],
}

/// A recorded battle: its resolution, the ordered action log, every committed turn's
/// receipt (a single `pre == prev.post` chain rooted at [`Arena::genesis`]), and the
/// dice-driven blows (for replay reverification).
pub struct FightRecord {
    /// How the battle resolved.
    pub outcome: Outcome,
    /// The ordered action log (for printing).
    pub log: Vec<FightEvent>,
    /// Every committed turn's receipt, in order (chains onto [`Arena::genesis`]).
    pub receipts: Vec<TurnReceipt>,
    /// The dice-driven blows, each reverifiable via [`reverify_draw`].
    pub blows: Vec<Hit>,
}

fn set_reg(cell: CellId, slot: u8, v: u64) -> Effect {
    Effect::SetField {
        cell,
        index: slot as usize,
        value: field_from_u64(v),
    }
}

fn set_heap(cell: CellId, key: u64, v: u64) -> Effect {
    Effect::SetField {
        cell,
        index: key as usize,
        value: field_from_u64(v),
    }
}

impl Arena {
    /// Deploy a fresh arena with default HP (heroes [`HERO_HP`], enemies [`ENEMY_HP`]).
    pub fn deploy(seed: u8) -> Arena {
        Arena::deploy_with_hp(seed, HERO_HP, ENEMY_HP)
    }

    /// Deploy a fresh arena with explicit per-team starting HP (used to stage a
    /// specific fight, e.g. a defeat scenario).
    pub fn deploy_with_hp(seed: u8, hero_hp: u64, enemy_hp: u64) -> Arena {
        let story = Arc::new(combat_compiled());
        let mut world =
            WorldCell::deploy_compiled(Arc::clone(&story), seed).expect("the arena deploys");

        let active = slot(&story, V_ACTIVE);
        let fspent = slot(&story, V_FSPENT);
        let mut dn = [0u8; 4];
        let mut gd = [0u8; 4];
        let mut st = [0u8; 4];
        for c in 0..N as usize {
            dn[c] = slot(&story, &dn_name(c as u8));
            gd[c] = slot(&story, &gd_name(c as u8));
            st[c] = slot(&story, &st_name(c as u8));
        }

        // Seed the register control state directly (genesis config — no turn).
        world.seed_var(V_FSPENT, Value::Int(0));
        world.seed_var(V_FBUDGET, Value::Int(FOCUS_BUDGET as i64));
        for c in 0..N {
            world.seed_var(&dn_name(c), Value::Int(0));
            world.seed_var(&gd_name(c), Value::Int(0));
            world.seed_var(&st_name(c), Value::Int(0));
        }

        // Dice-rolled initiative fixes turn order; seat `active` at the first to act.
        let inits = initiative_rolls(seed);
        let order = initiative_order(seed);
        world.seed_var(V_ACTIVE, Value::Int(order[0] as i64));

        // Seed the heap scalars via a real (permissive) setup turn: HP, poison, and
        // the heavy-cooldown round marker must be PRESENT for the teeth to bite.
        let cell = world.cell_id();
        let mut effects = Vec::new();
        for c in 0..N {
            let hp = if is_hero(c) { hero_hp } else { enemy_hp };
            effects.push(set_heap(cell, hp_key(c), hp));
            effects.push(set_heap(cell, poison_key(c), 0));
            effects.push(set_heap(cell, heavy_round_key(c), 0));
        }
        let genesis = world
            .apply_raw(M_SETUP, effects)
            .expect("the arena setup turn commits");

        Arena {
            world,
            story,
            order,
            inits,
            round: 1,
            seq: 0,
            genesis,
            active,
            fspent,
            dn,
            gd,
            st,
        }
    }

    /// The installed program descriptor (for introspecting the teeth).
    pub fn story(&self) -> &CompiledStory {
        &self.story
    }

    // ── committed-state reads ──
    /// Combatant `c`'s current HP.
    pub fn hp(&self, c: u8) -> u64 {
        self.world.read_heap(hp_key(c)).unwrap_or(0)
    }
    /// Combatant `c`'s poison stacks.
    pub fn poison(&self, c: u8) -> u64 {
        self.world.read_heap(poison_key(c)).unwrap_or(0)
    }
    /// Whether combatant `c` is downed.
    pub fn is_down(&self, c: u8) -> bool {
        self.world.read_var(&dn_name(c)) != 0
    }
    /// Whether combatant `c` is guarding.
    pub fn is_guarding(&self, c: u8) -> bool {
        self.world.read_var(&gd_name(c)) != 0
    }
    /// Whether combatant `c` is stunned.
    pub fn is_stunned(&self, c: u8) -> bool {
        self.world.read_var(&st_name(c)) != 0
    }
    /// Whose turn the `active` pointer currently names.
    pub fn active(&self) -> u8 {
        self.world.read_var(V_ACTIVE) as u8
    }
    /// The battle's resolution.
    pub fn outcome(&self) -> Outcome {
        let enemies_down = (0..N).filter(|&c| !is_hero(c)).all(|c| self.is_down(c));
        let heroes_down = (0..N).filter(|&c| is_hero(c)).all(|c| self.is_down(c));
        if enemies_down {
            Outcome::Victory
        } else if heroes_down {
            Outcome::Defeat
        } else {
            Outcome::Ongoing
        }
    }

    /// The next living combatant after `a` in initiative order, treating `also_down`
    /// as already downed (so the finish-that-downs-`t` hands off past `t`).
    fn next_active(&self, a: u8, also_down: Option<u8>) -> u8 {
        let pos = self.order.iter().position(|&x| x == a).unwrap_or(0);
        for k in 1..=N as usize {
            let cand = self.order[(pos + k) % N as usize];
            if Some(cand) != also_down && !self.is_down(cand) {
                return cand;
            }
        }
        a
    }

    // ── abilities (each a real committed turn or a real refusal) ──

    /// **A basic attack** — a verifiable `d8` draw bound into the turn. Refused if it
    /// is not `a`'s turn, `a` is stunned/downed, `t` is downed, or the blow would drop
    /// `t` below the HP floor.
    pub fn attack(&mut self, a: u8, t: u8) -> Result<Hit, WorldError> {
        self.strike(a, t, Ability::Attack)
    }

    /// **A heavy/special strike** — a higher-variance `d12` draw + poison + stun,
    /// costing focus and gated to once per round. Heroes only.
    pub fn heavy(&mut self, a: u8, t: u8) -> Result<Hit, WorldError> {
        self.strike(a, t, Ability::Heavy)
    }

    fn strike(&mut self, a: u8, t: u8, ability: Ability) -> Result<Hit, WorldError> {
        self.seq += 1;
        let req = combat_request(&self.world, self.seq, a, t, ability);
        let (roll, evidence) = roll_request(&req, ability.die());
        let guarded = self.is_guarding(t);
        let damage = damage_of_roll(roll, guarded);
        let hp_after = self.hp(t).saturating_sub(damage);
        let next = self.next_active(a, None);
        let cell = self.world.cell_id();
        let draw = CombatDraw {
            request: req,
            evidence,
            roll,
            damage,
            guarded,
            sides: ability.die(),
            attacker: a,
            target: t,
            ability,
        };

        let mut effects = vec![
            set_heap(cell, hp_key(t), hp_after),
            set_reg(cell, self.active, next as u64),
            // Acting spends this combatant's guard from the previous round.
            set_reg(cell, self.gd[a as usize], 0),
            dice_event_effect(cell, &draw),
        ];
        if ability == Ability::Heavy {
            let new_spent = self.world.read_var(V_FSPENT) + HEAVY_FOCUS_COST;
            let new_poison = self.poison(t) + HEAVY_POISON;
            effects.push(set_reg(cell, self.fspent, new_spent));
            effects.push(set_heap(cell, poison_key(t), new_poison));
            effects.push(set_heap(cell, heavy_round_key(a), self.round));
            effects.push(set_reg(cell, self.st[t as usize], 1)); // the heavy strike STUNS
        }

        let method = match ability {
            Ability::Attack => m_attack(a, t),
            Ability::Heavy => m_heavy(a, t),
        };
        let receipt = self.world.apply_raw(&method, effects)?;
        Ok(Hit {
            receipt,
            draw,
            target_hp_after: self.hp(t),
        })
    }

    /// **Guard** — brace: set `a`'s guard status (incoming damage reduced; `a` cannot
    /// be executed while guarding). Refused if it is not `a`'s turn.
    pub fn guard(&mut self, a: u8) -> Result<TurnReceipt, WorldError> {
        let next = self.next_active(a, None);
        let cell = self.world.cell_id();
        let effects = vec![
            set_reg(cell, self.gd[a as usize], 1),
            set_reg(cell, self.active, next as u64),
        ];
        self.world.apply_raw(&m_guard(a), effects)
    }

    /// **Execute** — down a WEAKENED target (`hp ≤ FINISH_THRESHOLD`, not guarding, not
    /// already downed). The down is write-once. Refused otherwise.
    pub fn finish(&mut self, a: u8, t: u8) -> Result<TurnReceipt, WorldError> {
        let next = self.next_active(a, Some(t));
        let cell = self.world.cell_id();
        let effects = vec![
            set_reg(cell, self.dn[t as usize], 1),
            set_reg(cell, self.gd[a as usize], 0),
            set_reg(cell, self.active, next as u64),
        ];
        self.world.apply_raw(&m_finish(a, t), effects)
    }

    /// **Pass** — yield the turn, clearing `a`'s own stun (how a stunned combatant
    /// recovers). Refused if it is not `a`'s turn.
    pub fn pass(&mut self, a: u8) -> Result<TurnReceipt, WorldError> {
        let next = self.next_active(a, None);
        let cell = self.world.cell_id();
        let effects = vec![
            set_reg(cell, self.st[a as usize], 0),
            set_reg(cell, self.gd[a as usize], 0),
            set_reg(cell, self.active, next as u64),
        ];
        self.world.apply_raw(&m_pass(a), effects)
    }

    /// **Poison tick** — a round-start system turn: `c` loses HP equal to its poison
    /// stacks, floored at 1 (poison grinds but does not itself kill). No turn order.
    pub fn poison_tick(&mut self, c: u8) -> Result<TurnReceipt, WorldError> {
        let hp_after = self.hp(c).saturating_sub(self.poison(c)).max(1);
        let cell = self.world.cell_id();
        self.world
            .apply_raw(&m_tick(c), vec![set_heap(cell, hp_key(c), hp_after)])
    }

    /// **Directly set the `active` pointer** (test scaffolding for staging an
    /// out-of-turn move). Not part of the ability surface.
    pub fn force_active(&mut self, c: u8) {
        self.world.seed_var(V_ACTIVE, Value::Int(c as i64));
    }

    // ── the driver AI: play a full fight to resolution ──

    /// Pick a living-opponent target for `a`, preferring a NON-guarding opponent, then
    /// lowest HP.
    fn choose_target(&self, a: u8) -> Option<u8> {
        opponents(a)
            .into_iter()
            .filter(|&t| !self.is_down(t))
            .min_by_key(|&t| (self.is_guarding(t) as u64, self.hp(t)))
    }

    /// The heavy strike is available to `a` against `t` iff `a` is a hero with focus
    /// remaining, off cooldown this round, and the blow will not floor the target.
    fn heavy_ok(&self, a: u8, t: u8) -> bool {
        is_hero(a)
            && self.world.read_var(V_FSPENT) + HEAVY_FOCUS_COST <= self.world.read_var(V_FBUDGET)
            && self.world.read_heap(heavy_round_key(a)).unwrap_or(0) < self.round
            && self.hp(t) > HEAVY_DIE
    }

    fn record(
        &self,
        log: &mut Vec<FightEvent>,
        receipts: &mut Vec<TurnReceipt>,
        actor: u8,
        kind: &'static str,
        target: Option<u8>,
        roll: Option<u64>,
        damage: Option<u64>,
        receipt: &TurnReceipt,
        note: String,
    ) {
        receipts.push(receipt.clone());
        log.push(FightEvent {
            round: self.round,
            actor,
            kind,
            target,
            roll,
            damage,
            turn_hash: receipt.turn_hash,
            note,
        });
    }

    /// Play out the active combatant `a`'s turn under the simple tactical AI, recording
    /// the committed turn (and, for a dice blow, the reverifiable [`Hit`]).
    fn take_turn(
        &mut self,
        a: u8,
        log: &mut Vec<FightEvent>,
        receipts: &mut Vec<TurnReceipt>,
        blows: &mut Vec<Hit>,
    ) {
        // A stunned combatant can only shake it off.
        if self.is_stunned(a) {
            let r = self.pass(a).expect("a stunned combatant may pass");
            let note = format!("{} shakes off the stun", name(a));
            self.record(log, receipts, a, "pass", None, None, None, &r, note);
            return;
        }
        let Some(t) = self.choose_target(a) else {
            let r = self.pass(a).expect("pass");
            let note = format!("{} finds no foe", name(a));
            self.record(log, receipts, a, "pass", None, None, None, &r, note);
            return;
        };

        // Execute a weakened, unguarded foe.
        if self.hp(t) <= FINISH_THRESHOLD && !self.is_guarding(t) {
            let r = self.finish(a, t).expect("executing a weakened foe commits");
            let note = format!("{} executes {}", name(a), name(t));
            self.record(log, receipts, a, "finish", Some(t), None, None, &r, note);
            return;
        }

        // A heavy strike if it is safe and affordable.
        if self.heavy_ok(a, t) {
            let h = self.heavy(a, t).expect("a heavy strike commits");
            let note = format!(
                "{} heavy-strikes {} for {} (poison+stun)",
                name(a),
                name(t),
                h.draw.damage
            );
            self.record(
                log,
                receipts,
                a,
                "heavy",
                Some(t),
                Some(h.draw.roll),
                Some(h.draw.damage),
                &h.receipt,
                note,
            );
            blows.push(h);
            return;
        }

        // A basic attack when the blow will not hit the HP floor; else brace (guard).
        let worst = damage_of_roll(ATTACK_DIE, self.is_guarding(t));
        if self.hp(t) > worst {
            let h = self.attack(a, t).expect("a survivable attack commits");
            let note = format!("{} strikes {} for {}", name(a), name(t), h.draw.damage);
            self.record(
                log,
                receipts,
                a,
                "attack",
                Some(t),
                Some(h.draw.roll),
                Some(h.draw.damage),
                &h.receipt,
                note,
            );
            blows.push(h);
        } else {
            let r = self.guard(a).expect("guard");
            let note = format!("{} braces (no safe strike)", name(a));
            self.record(log, receipts, a, "guard", None, None, None, &r, note);
        }
    }

    /// **Play the battle to resolution under the tactical AI.** The driver FOLLOWS the
    /// `active` pointer (each ability advances it to the next living combatant) — no
    /// out-of-band pokes, so the receipts form one clean `pre == prev.post` chain rooted
    /// at [`Self::genesis`]. A round boundary (the pointer wrapping back to an
    /// already-acted combatant) triggers a poison tick on each poisoned survivor.
    pub fn auto_fight(&mut self, max_turns: u64) -> FightRecord {
        let mut log = Vec::new();
        let mut receipts = Vec::new();
        let mut blows = Vec::new();
        let mut acted: std::collections::BTreeSet<u8> = Default::default();
        let mut turns = 0u64;

        while self.outcome() == Outcome::Ongoing && turns < max_turns {
            let a = self.active();
            if self.is_down(a) {
                break; // defensive: `active` should always name a living combatant
            }
            // A new round: the pointer wrapped back to someone who already acted.
            if acted.contains(&a) {
                self.round += 1;
                acted.clear();
                for c in 0..N {
                    if !self.is_down(c) && self.poison(c) > 0 {
                        let before = self.hp(c);
                        let r = self.poison_tick(c).expect("a poison tick commits");
                        let dealt = before - self.hp(c);
                        let note = format!("{} suffers {} poison", name(c), dealt);
                        self.record(
                            &mut log,
                            &mut receipts,
                            c,
                            "tick",
                            None,
                            None,
                            Some(dealt),
                            &r,
                            note,
                        );
                    }
                }
                if self.outcome() != Outcome::Ongoing {
                    break;
                }
            }
            acted.insert(a);
            self.take_turn(a, &mut log, &mut receipts, &mut blows);
            turns += 1;
        }

        FightRecord {
            outcome: self.outcome(),
            log,
            receipts,
            blows,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The installed program is default-deny with a real tooth on every ability: a
    /// legal move matches its case, and each mechanic's constraint is a genuine kernel
    /// predicate (introspected off the program).
    #[test]
    fn the_teeth_are_real_installed_kernel_predicates() {
        let story = combat_compiled();
        let CellProgram::Cases(cases) = &story.program else {
            panic!("combat program is Cases");
        };
        let find = |method: &str| {
            let m = symbol(method);
            cases
                .iter()
                .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: mm } if *mm == m))
                .unwrap_or_else(|| panic!("a case for `{method}`"))
                .constraints
                .clone()
        };

        // attack carries the HP floor + turn-order + attack-dead teeth.
        let atk = find(&m_attack(RANGER, WARDEN));
        assert!(
            atk.iter()
                .any(|c| matches!(c, StateConstraint::AllowedTransitions { .. })),
            "attack has the turn-order tooth"
        );
        assert!(
            atk.iter().any(|c| matches!(
                c,
                StateConstraint::HeapField { key, atom: HeapAtom::Gte { .. } } if *key == hp_key(WARDEN)
            )),
            "attack has the HP-floor tooth on the target"
        );

        // heavy carries the resource + cooldown teeth.
        let hvy = find(&m_heavy(RANGER, WARDEN));
        assert!(
            hvy.iter()
                .any(|c| matches!(c, StateConstraint::FieldLteField { .. })),
            "heavy has the focus resource tooth"
        );
        assert!(
            hvy.iter().any(|c| matches!(
                c,
                StateConstraint::HeapField { atom: HeapAtom::StrictMonotonic, key } if *key == heavy_round_key(RANGER)
            )),
            "heavy has the cooldown tooth"
        );

        // finish carries the weakened-only + write-once + no-guard teeth.
        let fin = find(&m_finish(RANGER, WARDEN));
        assert!(
            fin.iter().any(|c| matches!(
                c,
                StateConstraint::HeapField { atom: HeapAtom::Lte { .. }, key } if *key == hp_key(WARDEN)
            )),
            "finish requires a weakened target"
        );
        assert!(
            fin.iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { .. })),
            "finish downs write-once"
        );

        // enemies have no heavy (heroes-only special).
        let m = symbol(&m_heavy(WARDEN, RANGER));
        assert!(
            !cases
                .iter()
                .any(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: mm } if *mm == m)),
            "enemies have no heavy strike"
        );
    }

    /// A multi-combatant fight plays initiative-ordered rounds to a VICTORY, the
    /// receipts chain (`pre == prev.post`), and every dice-driven blow re-verifies.
    #[test]
    fn a_full_fight_plays_to_victory_chained_and_reverified() {
        let mut arena = Arena::deploy(7);

        // Initiative is dice-rolled and reproducible.
        assert_eq!(
            initiative_order(7),
            arena.order,
            "the arena seats the dice-rolled initiative order"
        );

        let rec = arena.auto_fight(400);
        assert_eq!(rec.outcome, Outcome::Victory, "the heroes win the fight");
        assert!(
            (0..N).filter(|&c| !is_hero(c)).all(|c| arena.is_down(c)),
            "every enemy is downed"
        );
        assert!(
            (0..N).filter(|&c| is_hero(c)).any(|c| !arena.is_down(c)),
            "at least one hero still stands"
        );

        // The fight exercised the full kit.
        let kinds: std::collections::BTreeSet<&str> = rec.log.iter().map(|e| e.kind).collect();
        for want in ["attack", "heavy", "finish"] {
            assert!(
                kinds.contains(want),
                "the fight used `{want}` (kinds: {kinds:?})"
            );
        }

        // Every dice-driven blow is bound into its receipt and RE-DERIVES the identical
        // roll on replay (the verifiable-dice tooth, across the whole fight).
        assert!(
            rec.blows.len() >= 3,
            "several dice blows landed ({})",
            rec.blows.len()
        );
        for h in &rec.blows {
            let rederived = reverify_draw(&h.receipt, &h.draw)
                .unwrap_or_else(|e| panic!("a fight blow re-verifies: {e}"));
            assert_eq!(
                rederived, h.draw.roll,
                "replay re-derives the identical roll"
            );
        }

        // The committed turns form a SINGLE receipt chain rooted at the setup turn:
        // each turn's pre-state hash is the previous turn's post-state hash.
        let mut prev = arena.genesis.post_state_hash;
        assert!(!rec.receipts.is_empty(), "the fight committed real turns");
        for (i, r) in rec.receipts.iter().enumerate() {
            assert_ne!(
                r.turn_hash, [0u8; 32],
                "turn {i} is a genuine committed turn"
            );
            assert_eq!(r.pre_state_hash, prev, "turn {i} chains: pre == prev.post");
            prev = r.post_state_hash;
        }
    }

    /// A dice blow binds its draw into the receipt and REPRODUCES on replay (the core
    /// verifiable-dice tooth, driven directly).
    #[test]
    fn a_dice_blow_binds_and_reverifies() {
        let mut arena = Arena::deploy(9);
        // Ranger strikes the Warden (make it the Ranger's turn).
        arena.force_active(RANGER);
        let hit = arena.attack(RANGER, WARDEN).expect("the attack commits");

        assert!(
            (1..=ATTACK_DIE).contains(&hit.draw.roll),
            "a real d8 face, got {}",
            hit.draw.roll
        );
        let bound = bound_draw(&hit.receipt).expect("the draw is bound into the receipt");
        assert_eq!(bound.roll, hit.draw.roll);
        assert_eq!(bound.damage, hit.draw.damage);

        let rederived =
            reverify_draw(&hit.receipt, &hit.draw).expect("the honest draw re-verifies");
        assert_eq!(
            rederived, hit.draw.roll,
            "replay re-derives the identical roll"
        );
    }

    /// **Acting OUT OF TURN is a real executor refusal.** With the `active` pointer on
    /// another combatant, the Ranger's attack fails the `AllowedTransitions` tooth and
    /// commits nothing (anti-ghost). The same attack on the Ranger's turn commits — so
    /// the tooth is non-vacuous.
    #[test]
    fn acting_out_of_turn_is_refused_but_in_turn_commits() {
        let mut arena = Arena::deploy(3);

        // Not the Ranger's turn.
        arena.force_active(WARDEN);
        let hp_before = arena.hp(WARDEN);
        let out = arena.attack(RANGER, WARDEN);
        assert!(
            matches!(out, Err(WorldError::Refused(_))),
            "attacking out of turn is refused, got {out:?}"
        );
        assert_eq!(arena.hp(WARDEN), hp_before, "anti-ghost: no damage dealt");
        assert_eq!(
            arena.active(),
            WARDEN,
            "anti-ghost: the turn pointer is unmoved"
        );

        // On the Ranger's turn the same attack commits (non-vacuous).
        arena.force_active(RANGER);
        arena
            .attack(RANGER, WARDEN)
            .expect("in-turn, the attack commits");
        assert!(arena.hp(WARDEN) < hp_before, "the in-turn blow landed");
    }

    /// **A lethal OVERKILL is refused by the HP floor.** With a target at 1 HP, any
    /// attack (damage ≥ 1) would underflow it below the floor — a real refusal that
    /// commits nothing. Seeding a healthy target instead lets the blow land (non-vacuous).
    #[test]
    fn a_lethal_overkill_is_refused_by_the_hp_floor() {
        let mut arena = Arena::deploy_with_hp(4, HERO_HP, 1); // enemies start at 1 HP
        arena.force_active(RANGER);
        assert_eq!(arena.hp(WARDEN), 1);

        let out = arena.attack(RANGER, WARDEN);
        assert!(
            matches!(out, Err(WorldError::Refused(_))),
            "a blow that underflows the HP floor is refused, got {out:?}"
        );
        assert_eq!(
            arena.hp(WARDEN),
            1,
            "anti-ghost: HP unchanged after the refusal"
        );

        // Against a healthy target the identical attack commits.
        let mut healthy = Arena::deploy_with_hp(4, HERO_HP, ENEMY_HP);
        healthy.force_active(RANGER);
        healthy
            .attack(RANGER, WARDEN)
            .expect("a survivable blow commits");
        assert!(
            healthy.hp(WARDEN) < ENEMY_HP,
            "the blow landed on a healthy foe"
        );
    }

    /// **Attacking a DOWNED target is refused.** Down the Hound (execute a weakened
    /// one), then an attack on it fails the `UntilEvent(dn)` tooth.
    #[test]
    fn attacking_a_downed_target_is_refused() {
        let mut arena = Arena::deploy_with_hp(5, HERO_HP, 4); // enemies weak enough to execute
        arena.force_active(RANGER);
        arena
            .finish(RANGER, HOUND)
            .expect("executing a weakened foe commits");
        assert!(arena.is_down(HOUND), "the Hound is downed");

        arena.force_active(CLERIC);
        let out = arena.attack(CLERIC, HOUND);
        assert!(
            matches!(out, Err(WorldError::Refused(_))),
            "attacking a downed foe is refused, got {out:?}"
        );
    }

    /// **Executing a HEALTHY target is refused** (the finish needs a weakened target);
    /// once whittled below the threshold, the execute commits (non-vacuous).
    #[test]
    fn executing_a_healthy_target_is_refused_then_a_weak_one_commits() {
        let mut arena = Arena::deploy_with_hp(6, HERO_HP, ENEMY_HP);
        arena.force_active(RANGER);
        assert!(arena.hp(WARDEN) > FINISH_THRESHOLD);

        let out = arena.finish(RANGER, WARDEN);
        assert!(
            matches!(out, Err(WorldError::Refused(_))),
            "executing a healthy foe is refused, got {out:?}"
        );
        assert!(!arena.is_down(WARDEN), "anti-ghost: not downed");

        // Whittle the Warden below the threshold, then the execute commits.
        let mut weak = Arena::deploy_with_hp(6, HERO_HP, FINISH_THRESHOLD);
        weak.force_active(RANGER);
        weak.finish(RANGER, WARDEN)
            .expect("a weakened foe can be executed");
        assert!(weak.is_down(WARDEN), "the weakened foe is downed");
    }

    /// **Executing a GUARDING target is refused** — the guard status is respected by the
    /// executor. Once the guard drops, the execute commits (non-vacuous).
    #[test]
    fn executing_a_guarding_target_is_refused() {
        let mut arena = Arena::deploy_with_hp(2, HERO_HP, FINISH_THRESHOLD);
        // The Warden guards on its turn.
        arena.force_active(WARDEN);
        arena.guard(WARDEN).expect("the Warden braces");
        assert!(arena.is_guarding(WARDEN));

        arena.force_active(RANGER);
        let out = arena.finish(RANGER, WARDEN);
        assert!(
            matches!(out, Err(WorldError::Refused(_))),
            "executing a guarding foe is refused, got {out:?}"
        );
        assert!(
            !arena.is_down(WARDEN),
            "anti-ghost: the guarding foe stands"
        );
    }

    /// **A STUNNED combatant cannot strike** (`UntilEvent(st)`); it may only pass, which
    /// clears the stun and lets it act next time.
    #[test]
    fn a_stunned_combatant_cannot_strike_until_it_passes() {
        let mut arena = Arena::deploy(8);
        // Ranger heavy-strikes the Warden → the Warden is stunned.
        arena.force_active(RANGER);
        arena
            .heavy(RANGER, WARDEN)
            .expect("the heavy strike commits");
        assert!(
            arena.is_stunned(WARDEN),
            "the heavy strike stunned the Warden"
        );

        // The stunned Warden cannot attack.
        arena.force_active(WARDEN);
        let out = arena.attack(WARDEN, RANGER);
        assert!(
            matches!(out, Err(WorldError::Refused(_))),
            "a stunned combatant cannot strike, got {out:?}"
        );

        // It passes (clearing the stun); afterwards it can act.
        arena.pass(WARDEN).expect("a stunned combatant may pass");
        assert!(!arena.is_stunned(WARDEN), "the pass cleared the stun");
        arena.force_active(WARDEN);
        arena
            .attack(WARDEN, RANGER)
            .expect("recovered, the Warden strikes");
    }

    /// **Overspending the focus resource is refused** (`FieldLteField`), and the heavy
    /// **cooldown** (once per round, `StrictMonotonic`) is a real refusal too.
    #[test]
    fn focus_overspend_and_heavy_cooldown_are_refused() {
        let mut arena = Arena::deploy(1);

        // First heavy in round 1 commits (focus 0→15, cooldown 0→1).
        arena.force_active(RANGER);
        arena.heavy(RANGER, WARDEN).expect("first heavy commits");

        // A second heavy by the Ranger in the SAME round fails the cooldown.
        arena.force_active(RANGER);
        let out = arena.heavy(RANGER, WARDEN);
        assert!(
            matches!(out, Err(WorldError::Refused(_))),
            "a second heavy in one round is refused by the cooldown, got {out:?}"
        );

        // Advance rounds and drain focus: cost 15, budget 40 ⇒ the 3rd heavy overspends.
        arena.round = 2;
        arena.force_active(RANGER);
        arena
            .heavy(RANGER, WARDEN)
            .expect("round 2 heavy commits (spent 15→30)");
        arena.round = 3;
        arena.force_active(RANGER);
        let out = arena.heavy(RANGER, WARDEN);
        assert!(
            matches!(out, Err(WorldError::Refused(_))),
            "the focus overspend (30+15 > 40) is refused, got {out:?}"
        );
    }

    /// **A FORGED (gentler) roll is caught on replay.** Take an honest blow, rewrite the
    /// roll+damage bound into the receipt to a gentle 1, and replay re-derives the true
    /// roll and catches the mismatch. The honest blow passes the same tooth (non-vacuous).
    #[test]
    fn a_forged_roll_is_caught_on_replay() {
        let mut arena = Arena::deploy(11);
        arena.force_active(RANGER);
        let honest = arena
            .attack(RANGER, WARDEN)
            .expect("an honest blow commits");
        assert_eq!(
            reverify_draw(&honest.receipt, &honest.draw).expect("honest re-verifies"),
            honest.draw.roll
        );
        assert!(honest.draw.roll > 1, "seed 11 rolls above the forge floor");

        // Forge a gentler blow: rewrite the bound roll+damage to 1 and re-link the draw.
        let mut receipt = honest.receipt.clone();
        let mut draw = honest.draw.clone();
        let topic = symbol(DICE_TOPIC);
        let ev = receipt
            .emitted_events
            .iter_mut()
            .find(|e| e.topic == topic)
            .expect("the dice event");
        ev.data[2] = field_from_u64(1);
        ev.data[3] = field_from_u64(1);
        draw.roll = 1;
        draw.damage = 1;

        let out = reverify_draw(&receipt, &draw);
        assert_eq!(
            out,
            Err(DiceReplayError::RollMismatch {
                bound: 1,
                rederived: honest.draw.roll,
            }),
            "the forged roll is caught, got {out:?}"
        );
    }

    /// A forged DAMAGE alone (roll left honest, damage lowered) is caught too.
    #[test]
    fn a_forged_damage_is_caught_on_replay() {
        let mut arena = Arena::deploy(12);
        arena.force_active(RANGER);
        let honest = arena.attack(RANGER, WARDEN).expect("an honest blow");
        assert!(honest.draw.damage > 1);

        let mut receipt = honest.receipt.clone();
        let topic = symbol(DICE_TOPIC);
        let ev = receipt
            .emitted_events
            .iter_mut()
            .find(|e| e.topic == topic)
            .expect("the dice event");
        ev.data[3] = field_from_u64(1); // forged damage; roll left honest

        let out = reverify_draw(&receipt, &honest.draw);
        assert_eq!(
            out,
            Err(DiceReplayError::DamageMismatch {
                bound: 1,
                expected: honest.draw.damage,
            }),
            "a forged damage is caught, got {out:?}"
        );
    }

    /// **The fight resolves to DEFEAT** when the heroes fall. Staged with a fragile
    /// party (heroes passive), the enemies grind and execute both heroes — a real
    /// resolution on the real chain.
    #[test]
    fn the_fight_can_resolve_to_defeat() {
        // Heroes start fragile; enemies healthy. The driver FOLLOWS `active` (a clean
        // chain) with a policy where the heroes yield and the enemies press the attack.
        let mut arena = Arena::deploy_with_hp(13, FINISH_THRESHOLD, ENEMY_HP);
        let mut turns = 0;
        while arena.outcome() == Outcome::Ongoing && turns < 200 {
            let a = arena.active();
            if arena.is_down(a) {
                break;
            }
            if is_hero(a) {
                arena.pass(a).expect("a hero yields");
                turns += 1;
                continue;
            }
            // Enemy: execute a weakened hero, else grind the weakest.
            let t = (0..N)
                .filter(|&h| is_hero(h) && !arena.is_down(h))
                .min_by_key(|&h| arena.hp(h));
            let Some(t) = t else { break };
            if arena.hp(t) <= FINISH_THRESHOLD && !arena.is_guarding(t) {
                arena.finish(a, t).expect("execute a fragile hero");
            } else if arena.hp(t) > damage_of_roll(ATTACK_DIE, arena.is_guarding(t)) {
                arena.attack(a, t).expect("grind the hero");
            } else {
                arena.finish(a, t).expect("execute the ground-down hero");
            }
            turns += 1;
        }
        assert_eq!(arena.outcome(), Outcome::Defeat, "the party is defeated");
        assert!((0..N).filter(|&c| is_hero(c)).all(|c| arena.is_down(c)));
    }
}
