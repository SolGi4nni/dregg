//! # The `.dungeon` validator — semantic soundness over any [`GameWorld`].
//!
//! A lift-and-shift port of `attested-dm/src/dungeon_dsl.rs`'s validator half, with
//! lint SEMANTICS and MESSAGES kept intact: dangling exit targets, an objective room
//! unreachable from `start`, a win item or gate item that is never placed, an NPC /
//! combat / spell in an unknown room, a spell with no learn source, consumables that
//! can never fire, and the advisory warnings (a flag-gate no rule sets, dialogue
//! addressing an absent NPC). Errors block [`super::parse::parse_dungeon`]; warnings
//! advise.

use std::collections::{BTreeSet, VecDeque};

use super::ir::{ConsumableEffect, DialogueGrant, GameWorld, Gate, SpellEffect};
use super::parse::Prov;

/// The weight of a validator [`Issue`]: an `Error` refuses the dungeon; a `Warning`
/// advises.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity {
    /// A defect that makes the dungeon unsound/unwinnable —
    /// [`super::parse::parse_dungeon`] refuses it.
    Error,
    /// An advisory an author probably wants to fix, but that does not block the parse.
    Warning,
}

/// **One finding from [`validate`]** — a severity and a legible, id-naming message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Issue {
    /// Whether this blocks (Error) or merely advises (Warning).
    pub severity: Severity,
    /// The human-legible description, naming the room/item/npc involved.
    pub message: String,
}

impl Issue {
    /// Whether this issue is a blocking [`Severity::Error`].
    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }
}

impl std::fmt::Display for Issue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tag = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        write!(f, "{tag}: {}", self.message)
    }
}

/// **Validate any [`GameWorld`]** (parsed or hand-written) and return every [`Issue`]
/// — errors (a dungeon that cannot be won/played) and warnings (advisories). An empty
/// result means the world is sound: reachable objective, every referenced item
/// obtainable, every actor in a real room, every spell learnable.
pub fn validate(world: &GameWorld) -> Vec<Issue> {
    check(world, None).into_iter().map(|(_, i)| i).collect()
}

/// The shared body of [`validate`] and [`super::parse::parse_dungeon`]'s semantic
/// gate: every finding, each with the source line the parser recorded for the
/// offending construct (when provenance is available).
pub(crate) fn check(world: &GameWorld, prov: Option<&Prov>) -> Vec<(Option<usize>, Issue)> {
    let mut out: Vec<(Option<usize>, Issue)> = Vec::new();
    // Macros (not closures) so several emitters can coexist without overlapping
    // `&mut out` borrows.
    macro_rules! err {
        ($line:expr, $msg:expr $(,)?) => {
            out.push((
                $line,
                Issue {
                    severity: Severity::Error,
                    message: $msg,
                },
            ))
        };
    }
    let obtainable = world.all_items();
    let room_ids: BTreeSet<&String> = world.rooms.keys().collect();

    // Start room must exist.
    if !world.rooms.contains_key(&world.start) {
        err!(
            prov.map(|p| p.start_line),
            format!("start room `{}` does not exist", world.start),
        );
    }

    // Dangling exits.
    for room in world.rooms.values() {
        for (dir, exit) in &room.exits {
            if !room_ids.contains(&exit.to_room) {
                let line =
                    prov.and_then(|p| p.exit_line.get(&(room.id.clone(), dir.clone())).copied());
                err!(
                    line,
                    format!(
                        "exit `{dir}` in room `{}` leads to unknown room `{}`",
                        room.id, exit.to_room
                    ),
                );
            }
            // A gate needing an item that exists nowhere.
            if let Some(Gate::NeedsItem(item)) = &exit.gate {
                if !obtainable.contains(item) {
                    let line = prov
                        .and_then(|p| p.exit_line.get(&(room.id.clone(), dir.clone())).copied());
                    err!(
                        line,
                        format!(
                            "gate on exit `{dir}` (room `{}`) needs item `{item}`, which exists nowhere",
                            room.id
                        ),
                    );
                }
            }
        }
    }

    // Objective room + win item.
    if !world.rooms.contains_key(&world.objective.room) {
        err!(
            prov.map(|p| p.objective_line),
            format!("objective room `{}` does not exist", world.objective.room),
        );
    } else if reachable(world).contains(&world.objective.room) {
        // reachable — fine
    } else {
        err!(
            prov.map(|p| p.objective_line),
            format!(
                "objective room `{}` is unreachable from start `{}`",
                world.objective.room, world.start
            ),
        );
    }
    // The win item must be obtainable from a room REACHABLE from start — existing
    // SOMEWHERE (`all_items`) is not enough: an item placed only in a
    // graph-disconnected room makes the objective unwinnable. Mirror `all_items` but
    // restricted to reachable rooms (gates ignored, like `reachable` — a
    // gated-but-connected room is still solvable).
    let reach = reachable(world);
    let mut reachable_items: BTreeSet<&str> = BTreeSet::new();
    for (id, room) in &world.rooms {
        if reach.contains(id) {
            reachable_items.extend(room.items.iter().map(String::as_str));
        }
    }
    for r in &world.dialogue {
        if reach.contains(&r.room) {
            if let DialogueGrant::GivesItem(i) = &r.grant {
                reachable_items.insert(i.as_str());
            }
        }
    }
    for r in &world.spell_rules {
        if reach.contains(&r.room) {
            if let SpellEffect::Conjure(i) = &r.effect {
                reachable_items.insert(i.as_str());
            }
        }
    }
    if !obtainable.contains(&world.objective.holding) {
        err!(
            prov.map(|p| p.objective_line),
            format!(
                "objective requires holding `{}`, which is never placed in any room",
                world.objective.holding
            ),
        );
    } else if !reachable_items.contains(world.objective.holding.as_str()) {
        err!(
            prov.map(|p| p.objective_line),
            format!(
                "objective requires holding `{}`, which is placed only in a room unreachable from start `{}`",
                world.objective.holding, world.start
            ),
        );
    }

    // Actors in unknown rooms.
    for h in world.hostiles.values() {
        if !room_ids.contains(&h.room) {
            err!(
                prov.and_then(|p| p.hostile_line.get(&h.room).copied()),
                format!(
                    "hostile `{}` is placed in unknown room `{}`",
                    h.name, h.room
                ),
            );
        }
    }
    for c in world.combat.values() {
        if !room_ids.contains(&c.room) {
            err!(
                prov.and_then(|p| p.combat_line.get(&c.room).copied()),
                format!(
                    "combat foe `{}` is placed in unknown room `{}`",
                    c.name, c.room
                ),
            );
        }
    }
    for n in &world.npcs {
        if !room_ids.contains(&n.room) {
            err!(
                prov.and_then(|p| p.npc_line.get(&n.id).copied()),
                format!("npc `{}` is placed in unknown room `{}`", n.id, n.room),
            );
        }
    }
    for (idx, r) in world.dialogue.iter().enumerate() {
        if !room_ids.contains(&r.room) {
            err!(
                prov.and_then(|p| p.dialogue_line.get(idx).copied()),
                format!(
                    "dialogue for npc `{}` names unknown room `{}`",
                    r.npc, r.room
                ),
            );
        }
    }
    for (idx, r) in world.spell_rules.iter().enumerate() {
        let line = prov.and_then(|p| p.spellrule_line.get(idx).copied());
        if !room_ids.contains(&r.room) {
            err!(
                line,
                format!(
                    "spell-rule for `{}` names unknown room `{}`",
                    r.spell, r.room
                ),
            );
        }
        if !world.is_spell_word(&r.spell) {
            err!(
                line,
                format!("spell-rule casts undeclared word `{}`", r.spell),
            );
        }
    }
    for (idx, u) in world.use_rules.iter().enumerate() {
        if !room_ids.contains(&u.room) {
            err!(
                prov.and_then(|p| p.use_line.get(idx).copied()),
                format!("use-rule for `{}` names unknown room `{}`", u.item, u.room),
            );
        }
    }

    // Consumables: the consumed item must be obtainable somewhere (never placed = an
    // item the player can never drink), and a status grant/cure must name a DECLARED
    // status flag (else the buff/debuff it promises does nothing). Both are blocking
    // errors — a broken consumable is not a playable dungeon.
    let status_flags: BTreeSet<&str> = world.statuses.iter().map(|s| s.flag.as_str()).collect();
    for (idx, c) in world.consumables.iter().enumerate() {
        let line = prov.and_then(|p| p.consumable_line.get(idx).copied());
        if !obtainable.contains(&c.item) {
            err!(
                line,
                format!(
                    "consumable `{}` is never placed in any room (it can never be used)",
                    c.item
                ),
            );
        }
        match &c.effect {
            ConsumableEffect::Status { flag, .. } => {
                if !status_flags.contains(flag.as_str()) {
                    err!(
                        line,
                        format!(
                            "consumable `{}` grants status `{flag}`, which no `status` line declares",
                            c.item
                        ),
                    );
                }
            }
            ConsumableEffect::Cure(flag) => {
                if !status_flags.contains(flag.as_str()) {
                    err!(
                        line,
                        format!(
                            "consumable `{}` cures status `{flag}`, which no `status` line declares",
                            c.item
                        ),
                    );
                }
            }
            _ => {}
        }
    }

    // Every flag that some rule can SET — a spell's learn-by-flag needs a source in
    // here.
    let mut settable: BTreeSet<String> = BTreeSet::new();
    for u in &world.use_rules {
        settable.insert(u.sets_flag.0.clone());
    }
    for h in world.hostiles.values() {
        settable.insert(h.victory_flag.0.clone());
    }
    for c in world.combat.values() {
        settable.insert(c.victory_flag.0.clone());
    }
    for r in &world.dialogue {
        if let DialogueGrant::OpensFlag(k, _) = &r.grant {
            settable.insert(k.clone());
        }
    }
    for r in &world.spell_rules {
        match &r.effect {
            SpellEffect::SetFlag(k, _) | SpellEffect::Buff(k, _) => {
                settable.insert(k.clone());
            }
            SpellEffect::Conjure(_) => {}
        }
    }
    // A consumable that sets a flag / grants or cures a status is a source for that
    // flag; a status flag is also written by the engine (per-step decrement) — so an
    // author may legitimately gate on one without the "permanently sealed" warning
    // firing.
    for c in &world.consumables {
        match &c.effect {
            ConsumableEffect::SetFlag(k, _)
            | ConsumableEffect::Status { flag: k, .. }
            | ConsumableEffect::Cure(k) => {
                settable.insert(k.clone());
            }
            ConsumableEffect::Heal(_) | ConsumableEffect::Reveal => {}
        }
    }
    for s in &world.statuses {
        settable.insert(s.flag.clone());
    }

    // Spells: a learn source must exist.
    for s in &world.spells {
        let line = prov.and_then(|p| p.spell_line.get(&s.word).copied());
        match &s.learned {
            None => {}
            Some(Gate::NeedsItem(item)) => {
                if !obtainable.contains(item) {
                    err!(
                        line,
                        format!(
                            "spell `{}` is learned by holding `{item}`, which is never placed",
                            s.word
                        ),
                    );
                }
            }
            Some(Gate::NeedsFlag(flag, _)) => {
                if !settable.contains(flag) {
                    err!(
                        line,
                        format!(
                            "spell `{}` is learned via flag `{flag}`, but no rule ever sets that flag",
                            s.word
                        ),
                    );
                }
            }
        }
    }

    // Flag-gates whose flag NO declared rule sets → likely a permanently-sealed door /
    // dead topic. A WARNING, not an error: the engine also sets some flags internally
    // (light `<lamp>_oil`, combat wounds, the stranded flag), which an author MAY
    // legitimately gate on — so we surface the suspicion without ever false-blocking a
    // valid exotic design.
    for room in world.rooms.values() {
        for (dir, exit) in &room.exits {
            if let Some(Gate::NeedsFlag(flag, _)) = &exit.gate {
                if !settable.contains(flag) {
                    let line = prov
                        .and_then(|p| p.exit_line.get(&(room.id.clone(), dir.clone())).copied());
                    out.push((
                        line,
                        Issue {
                            severity: Severity::Warning,
                            message: format!(
                                "exit `{dir}` (room `{}`) is gated on flag `{flag}`, which no declared rule sets — it may be permanently sealed",
                                room.id
                            ),
                        },
                    ));
                }
            }
        }
    }
    for r in &world.dialogue {
        if let Some(Gate::NeedsFlag(flag, _)) = &r.requires {
            if !settable.contains(flag) {
                out.push((
                    None,
                    Issue {
                        severity: Severity::Warning,
                        message: format!(
                            "dialogue topic `{}` (npc `{}`) requires flag `{flag}`, which no declared rule sets",
                            r.topic, r.npc
                        ),
                    },
                ));
            }
        }
    }

    // Referenced-but-unobtainable items (weapons, armor, fuels, gate/dialogue
    // requirements).
    macro_rules! ref_item {
        ($item:expr, $ctx:expr) => {{
            let item: &str = $item;
            if !item.is_empty() && !obtainable.contains(item) {
                let ctx: String = $ctx;
                out.push((
                    None,
                    Issue {
                        severity: Severity::Error,
                        message: format!(
                            "item `{item}` is referenced ({ctx}) but never placed or obtainable"
                        ),
                    },
                ));
            }
        }};
    }
    for h in world.hostiles.values() {
        ref_item!(&h.defeated_by, format!("the weapon vs `{}`", h.name));
    }
    for c in world.combat.values() {
        ref_item!(&c.armed_by, format!("the weapon vs `{}`", c.name));
        if let Some((armor, _)) = &c.armor {
            ref_item!(armor, format!("armor vs `{}`", c.name));
        }
    }
    for u in &world.use_rules {
        ref_item!(&u.item, format!("the item used in `{}`", u.room));
    }
    if let Some(light) = &world.light {
        ref_item!(&light.lamp, "the lamp".to_string());
        for rf in &light.refuels {
            ref_item!(&rf.fuel_item, "lamp fuel".to_string());
        }
    }
    for r in &world.dialogue {
        if let Some(Gate::NeedsItem(item)) = &r.requires {
            ref_item!(item, format!("required to talk to `{}`", r.npc));
        }
    }

    // ── Warnings (advisory, non-blocking). ──
    // Dialogue that addresses an npc not standing in its room.
    for r in &world.dialogue {
        if room_ids.contains(&r.room) && !world.npc_here(&r.room, &r.npc) {
            out.push((
                None,
                Issue {
                    severity: Severity::Warning,
                    message: format!(
                        "dialogue topic `{}` addresses npc `{}`, who does not stand in room `{}`",
                        r.topic, r.npc, r.room
                    ),
                },
            ));
        }
    }

    out
}

/// Rooms reachable from `start` by following exits (gates ignored — a gate is a
/// puzzle, not a disconnection). Used to catch an objective that no path can ever
/// reach.
pub(crate) fn reachable(world: &GameWorld) -> BTreeSet<String> {
    let mut seen = BTreeSet::new();
    let mut q = VecDeque::new();
    if world.rooms.contains_key(&world.start) {
        seen.insert(world.start.clone());
        q.push_back(world.start.clone());
    }
    while let Some(id) = q.pop_front() {
        if let Some(room) = world.rooms.get(&id) {
            for exit in room.exits.values() {
                if world.rooms.contains_key(&exit.to_room) && seen.insert(exit.to_room.clone()) {
                    q.push_back(exit.to_room.clone());
                }
            }
        }
    }
    seen
}
