//! # `dialogue` — real NPC ROLEPLAY on the REAL executor: an NPC you TALK to, who REMEMBERS.
//!
//! The crate's other universes are things you FIGHT / LOOT / DESCEND. This module brings the
//! missing social half — **characters you converse with** — onto the same real substrate, by
//! re-homing `attested-dm`'s PROVEN dialogue design (its `Npc` / `DialogueRule`
//! / `DialogueGrant` — "ask NPC about TOPIC", a disposition/topic model where an NPC's WORDS can
//! DO something) off its toy blake3 ledger onto `spween-dregg`'s real
//! [`WorldCell`](spween_dregg::WorldCell) / [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor),
//! exactly how [`crate::overworld`] and [`crate::progression`] re-homed the map and the character
//! sheet.
//!
//! ## The design that is re-homed (attested-dm → the real cell)
//!
//! In `attested-dm`, talking is a closed `GameAction::Use` addressed to an NPC; the world's
//! `DialogueRule` (not the AI's prose) decides what the NPC's words DO — give a
//! (world-registered) item, open a gate flag, or merely reveal a fact
//! (`DialogueGrant::GivesItem` / `OpensFlag` / `Reveals`) — and only when the rule's `requires`
//! world-condition holds. That is the whole social-level anti-forgery tooth: *a jailbroken
//! narrator that makes the NPC "press the master key into your hand" changes nothing.* The
//! `requires` condition, in `attested-dm`, is checked against its toy `WorldCell`. Here it becomes
//! a **real [`StateConstraint`] the verified executor re-checks on the turn's post-state**, and the
//! NPC's regard becomes **real committed cell state**.
//!
//! ## The NPC's memory is a real on-ledger state gate
//!
//! "The Lantern-Keeper's Vigil": the `Npc`-equivalent Keeper guards a
//! bridge you must talk your way across. The keep-scene compiles to a real world-cell whose owned
//! slots ARE the Keeper's memory of you:
//!
//! | slot            | the Keeper remembers            | tooth (executor-enforced `StateConstraint`)                 |
//! |-----------------|---------------------------------|-------------------------------------------------------------|
//! | `disposition`   | how warmly they regard you      | warmth GATES the friendly line ([`FieldGte`]); rise-only    |
//! | `menace`        | whether you threatened them     | [`WriteOnce`]; a goad, once made, is remembered forever     |
//! | `topic_history` | you've unlocked the lore topic  | [`WriteOnce`]; gated on warmth + never-goaded               |
//! | `topic_secret`  | you've unlocked the deep topic  | [`BoundedBy`] — cannot be raised until `topic_history` is set|
//! | `passage_open`  | the Keeper opened the way        | [`WriteOnce`]; the GRANT, gated on warmth + the secret      |
//! | `oil_given`     | the Keeper filled your flask     | [`WriteOnce`]; the item grant (a `GivesItem`, re-homed)     |
//!
//! Every dialogue turn is one real cap-bounded turn that ADVANCES this state on a committed
//! `TurnReceipt`, and every later line is GATED on it by a kernel predicate — so the NPC
//! genuinely "remembers" on-ledger:
//!
//! * a **hostile-disposition** Keeper REFUSES the friendly topic ([`FieldGte`] on `disposition`),
//!   and a **warmed** Keeper REFUSES the goad ([`FieldLte`] on `disposition`) — the friendly and
//!   hostile paths gate each other's lines;
//! * a **locked topic** cannot be raised until its prerequisite is unlocked ([`BoundedBy`]:
//!   `topic_secret` may only be set while `topic_history` is non-zero);
//! * the **dialogue grant** (the Keeper filling your flask and lifting the chain) is a real gated
//!   effect ([`FieldGte`] on warmth AND on the secret) — no flattery moves the Keeper early,
//!   because talking is narration and the world grants only what the rule permits;
//! * a **goad**, once made, is remembered ([`WriteOnce`] `menace`) and permanently closes the
//!   friendly topic ([`FieldEquals`]`(menace, 0)`) — the social memory bites across the whole
//!   conversation.
//!
//! An out-of-context / forged line (a line driven outside its gate) is a real
//! [`WorldError::Refused`](spween_dregg::WorldError) that commits NOTHING (anti-ghost), and a
//! forged conversation RECORD (a line retconned out of its gate order) fails
//! [`verify_by_replay`](spween_dregg::verify_by_replay) — the same replay tooth every universe
//! ships.
//!
//! ## The narrator-voicing hook (real, not a hard dep)
//!
//! [`keeper_line`] reads the Keeper's committed state and returns the WORLD's canonical line for a
//! topic — the granted account when the rule fires, the withheld account when it does not — plus a
//! `voiced_prompt` a narrator brain ([`crate::narrator`]) MAY expand into vivid speech. It mirrors
//! `attested-dm`'s `granted_narration` / `withheld_narration` split. It is a pure read over
//! committed cell state: the narrator can call it, but nothing here depends on the narrator (prose
//! is not power — the voiced line cannot change what the gate already decided).
//!
//! ## Honest scope
//!
//! * The Keeper's memory (`disposition` / `menace` / the topic + grant flags) is REAL committed
//!   cell state; each dialogue turn is a REAL cap-bounded turn; each gate is a REAL
//!   executor-enforced `StateConstraint` — driven NON-VACUOUSLY in [`mod tests`] (each tooth is
//!   refused then admitted, one state change the only difference; it bites BOTH ways).
//! * This is a SINGLE NPC cell — one serial writer under one owner key (the same single-cell
//!   envelope the crate root's "CEILINGS" section names). A conversation with several NPCs whose
//!   dispositions cross-reference (a faction that turns cold when its ally is slighted) is the
//!   cross-cell frontier ([`crate::multicell`]'s `ObservedFieldEquals`), not this slice.
//! * The lines are a FIXED, world-authored menu (the closed typed channel `attested-dm` insists
//!   on — the NPC can only DO what a rule permits). FREEFORM player intents, and AI-DRIVEN NPC
//!   replies parsed back to a typed line via the confined brain, are the fuller-roleplay layer
//!   above: they would ride [`crate::narrator`]'s un-jailbreakable "the brain PROPOSES a typed
//!   command, the world DISPOSES" seam, choosing WHICH menu line to voice — never widening what a
//!   line can DO. FACTION REPUTATION is the multi-cell disposition graph noted above. All three are
//!   named seams over this real core, not gaps in it.
//!
//! [`FieldGte`]: dregg_app_framework::StateConstraint::FieldGte
//! [`FieldLte`]: dregg_app_framework::StateConstraint::FieldLte
//! [`FieldEquals`]: dregg_app_framework::StateConstraint::FieldEquals
//! [`WriteOnce`]: dregg_app_framework::StateConstraint::WriteOnce
//! [`BoundedBy`]: dregg_app_framework::StateConstraint::BoundedBy

use dregg_app_framework::{CellProgram, StateConstraint, TransitionGuard, field_from_u64, symbol};
use spween::Scene;
use spween_dregg::{CompiledStory, WorldCell, choice_method, compile_scene, parse};

// ── The Keeper — the NPC's identity (the attested-dm `Npc`, re-homed) ─────────────

/// The room the whole conversation happens in (the bridgehead the Keeper holds).
pub const ROOM_BRIDGE: &str = "bridge";
/// The room beyond the bridge — reached only once the Keeper opens the way (the WIN).
pub const ROOM_ACROSS: &str = "across";

/// The NPC's stable id — the `attested-dm` `Npc::id`, the conversation's target. Voiced by
/// the narrator hook; the executor speaks only in this cell's slots.
pub const KEEPER_ID: &str = "lantern-keeper";
/// The NPC's display name.
pub const KEEPER_NAME: &str = "The Lantern-Keeper";
/// The world's own account of who the Keeper is (the AI narrates AROUND this; it never overrides
/// what a gate decides).
pub const KEEPER_DESC: &str = "A silent warden at the bridgehead, wick trimmed low, who reads a traveller before a word is spoken.";

// ── The Vigil scene — the conversation as a real spween scene ─────────────────────

/// **"The Lantern-Keeper's Vigil" — the conversation, in the spween narrative DSL.** One room
/// (`bridge`) where every dialogue line is a self-looping choice (a real turn that stays in the
/// conversation), plus the `across` room reached only once the Keeper opens the way. The Keeper
/// begins wary (`disposition = 3`); the scene conditions the compiler CAN lower (`{ disposition >=
/// 4 }` on the friendly topic, `{ passage_open >= 1 }` on the crossing) become real executor teeth
/// directly, and [`vigil_compiled`] AUGMENTS the richer social teeth (the hostile `FieldLte`, the
/// `BoundedBy` topic lock, the `WriteOnce` memory flags, the gated grant) the v0 compiler does not
/// emit — exactly the [`crate::keep_compiled`] / [`crate::vault_compiled`] idiom.
pub const VIGIL: &str = r#"---
id: lantern-keepers-vigil
title: The Lantern-Keeper's Vigil
weight: 1
---

=== bridge

~ disposition = 3

The Lantern-Keeper stands at the bridgehead, a trimmed wick guttering low behind horn
glass. The chain across the span is up. The Keeper regards you and says nothing yet.

* [Offer a warm, honest greeting]
  ~ disposition += 1
  -> bridge

* [Goad the Keeper, a hand on your hilt]
  ~ menace = 1
  -> bridge

* [Ask about the lighthouse's history] { disposition >= 4 }
  ~ topic_history = 1
  -> bridge

* [Ask after the lantern's secret]
  ~ topic_secret = 1
  -> bridge

* [Beg the Keeper's leave to cross]
  ~ oil_given = 1
  ~ passage_open = 1
  -> bridge

* [Cross the lit bridge] { passage_open >= 1 }
  -> across

=== across

The chain falls away and the Keeper lifts the lantern to light your first steps. The far
dark waits, warmer for a friend at your back.

* [Step across into the lit dark]
  ~ gold += 1
  -> END
"#;

// ── Line coordinates (the driver + verifier speak in these) ───────────────────────

/// `bridge`: offer a warm greeting — raises `disposition` (the only line that warms the Keeper).
pub const LN_GREET: usize = 0;
/// `bridge`: goad the Keeper — sets `menace` (a `WriteOnce` the Keeper remembers). Gated on a LOW
/// disposition (augmented `FieldLte`): a warmed Keeper refuses to be threatened.
pub const LN_GOAD: usize = 1;
/// `bridge`: ask about the lighthouse's history — the friendly topic. Gated on warmth
/// (`{ disposition >= 4 }`, compiled) AND on never having goaded (augmented `FieldEquals(menace,
/// 0)`); unlocks `topic_history`.
pub const LN_ASK_HISTORY: usize = 2;
/// `bridge`: ask after the lantern's secret — the LOCKED topic. Cannot be raised until
/// `topic_history` is unlocked (augmented `BoundedBy`); unlocks `topic_secret`.
pub const LN_ASK_SECRET: usize = 3;
/// `bridge`: beg leave to cross — the GRANT. Gated on warmth (`FieldGte(disposition, 5)`) AND the
/// secret (`FieldGte(topic_secret, 1)`); sets `oil_given` (the item) + `passage_open` (the way).
pub const LN_BEG_LEAVE: usize = 4;
/// `bridge`: cross the lit bridge — the WIN. Gated on the Keeper having opened the way
/// (`{ passage_open >= 1 }`, compiled).
pub const LN_CROSS: usize = 5;
/// `across`: step across into the lit dark (ends the vigil).
pub const AC_STEP: usize = 0;

/// The warmth floor the friendly topic requires (`disposition >= 4`) — reached in one greeting
/// from the wary start (3).
pub const HISTORY_DISPOSITION_FLOOR: u64 = 4;
/// The warmth floor the Keeper's grant requires (`disposition >= 5`) — reached in two greetings.
pub const GRANT_DISPOSITION_FLOOR: u64 = 5;

/// Parse the Vigil scene.
pub fn vigil_scene() -> Scene {
    parse(VIGIL, "lantern-keepers-vigil.scene").expect("the vigil scene parses")
}

// ── Compiling the social teeth (the attested-dm `requires` → real `StateConstraint`) ──

/// Look up a var's compiled cell slot (panics on an unnamed var — every var below is named by an
/// effect/condition in [`VIGIL`], so it always resolves). Mirrors the crate's `keep_slot`.
fn vigil_slot(story: &CompiledStory, name: &str) -> u8 {
    (*story
        .var_slots
        .get(name)
        .unwrap_or_else(|| panic!("vigil var `{name}` has a compiled slot"))) as u8
}

/// Append `extra` constraints onto the compiled method-guarded case for `method` (a social tooth
/// the v0 compiler does not emit). Panics on a coordinate typo (no such case). Mirrors
/// the crate's `augment_case`; an augmented case is enforced identically to a compiled one —
/// the executor never distinguishes who authored a [`TransitionCase`].
fn augment_case(program: &mut CellProgram, method: &str, extra: Vec<StateConstraint>) {
    let m = symbol(method);
    let CellProgram::Cases(cases) = program else {
        panic!("vigil program is Cases");
    };
    let case = cases
        .iter_mut()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: mm } if *mm == m))
        .unwrap_or_else(|| panic!("no compiled case for method `{method}`"));
    case.constraints.extend(extra);
}

/// **Compile the Vigil AND augment its program with the social teeth.** The warmth gate on the
/// friendly topic (`FieldGte(disposition, 4)`) and the crossing gate (`FieldGte(passage_open, 1)`)
/// are already compiler-emitted from the scene conditions; this adds the shapes the v0 compiler
/// does not express:
///
/// * `LN_GOAD` — `FieldLte(disposition, 3)` (a warmed Keeper refuses the threat) + `WriteOnce`
///   `menace` (the goad, once made, is remembered);
/// * `LN_ASK_HISTORY` — `FieldEquals(menace, 0)` (a goad permanently closes the friendly topic) +
///   `WriteOnce` `topic_history`;
/// * `LN_ASK_SECRET` — `BoundedBy { topic_secret <- topic_history }` (the deep topic is locked
///   until the lore topic is unlocked) + `WriteOnce` `topic_secret`;
/// * `LN_BEG_LEAVE` — `FieldGte(disposition, 5)` + `FieldGte(topic_secret, 1)` (the grant is gated
///   on warmth AND the secret) + `WriteOnce` on `passage_open` and `oil_given`.
///
/// The result is a [`CellProgram`] the real executor enforces line-for-line.
pub fn vigil_compiled() -> CompiledStory {
    let mut story = compile_scene(&vigil_scene()).expect("the vigil compiles");

    let disposition = vigil_slot(&story, "disposition");
    let menace = vigil_slot(&story, "menace");
    let topic_history = vigil_slot(&story, "topic_history");
    let topic_secret = vigil_slot(&story, "topic_secret");
    let passage_open = vigil_slot(&story, "passage_open");
    let oil_given = vigil_slot(&story, "oil_given");

    // LN_GOAD — a hostile line, admitted only while the Keeper is NOT yet warmed
    // (`disposition <= 3`), and remembered forever once made (`WriteOnce` menace). This is the
    // mirror of the friendly topic's `FieldGte`: the two paths gate each other's lines.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BRIDGE, LN_GOAD),
        vec![
            StateConstraint::FieldLte {
                index: disposition,
                value: field_from_u64(HISTORY_DISPOSITION_FLOOR - 1),
            },
            StateConstraint::WriteOnce { index: menace },
        ],
    );

    // LN_ASK_HISTORY — the friendly topic. The compiled `FieldGte(disposition, 4)` already bars a
    // hostile Keeper; this adds `FieldEquals(menace, 0)` (a goad, once remembered, permanently
    // closes the friendly path) and `WriteOnce` on the unlocked-topic flag.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BRIDGE, LN_ASK_HISTORY),
        vec![
            StateConstraint::FieldEquals {
                index: menace,
                value: field_from_u64(0),
            },
            StateConstraint::WriteOnce {
                index: topic_history,
            },
        ],
    );

    // LN_ASK_SECRET — the LOCKED topic. `BoundedBy` admits the write ONLY while the witness
    // (`topic_history`) is non-zero: the deep topic cannot be raised until the lore topic is
    // unlocked. Plus `WriteOnce` on the secret flag.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BRIDGE, LN_ASK_SECRET),
        vec![
            StateConstraint::BoundedBy {
                index: topic_secret,
                witness_index: topic_history,
            },
            StateConstraint::WriteOnce {
                index: topic_secret,
            },
        ],
    );

    // LN_BEG_LEAVE — the GRANT (the attested-dm `DialogueGrant::GivesItem` + `OpensFlag`,
    // re-homed): the Keeper fills your flask (`oil_given`) and lifts the chain (`passage_open`)
    // ONLY when sufficiently won-over (`disposition >= 5`) AND you have learned the secret
    // (`topic_secret >= 1`). No flattery moves the Keeper early — the world grants only what the
    // rule permits. Both flags `WriteOnce` (the grant, once given, stands).
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BRIDGE, LN_BEG_LEAVE),
        vec![
            StateConstraint::FieldGte {
                index: disposition,
                value: field_from_u64(GRANT_DISPOSITION_FLOOR),
            },
            StateConstraint::FieldGte {
                index: topic_secret,
                value: field_from_u64(1),
            },
            StateConstraint::WriteOnce {
                index: passage_open,
            },
            StateConstraint::WriteOnce { index: oil_given },
        ],
    );

    story
}

/// **Deploy the Vigil as a real world-cell** (the social teeth installed as executor predicates).
/// Deterministic in `seed` (re-deploy reproduces the same identity + state hashes, what the replay
/// verifier leans on). The Keeper begins wary; only real dialogue turns warm them.
pub fn deploy_vigil(seed: u8) -> WorldCell {
    use std::sync::Arc;
    WorldCell::deploy_compiled(Arc::new(vigil_compiled()), seed).expect("the vigil deploys")
}

/// The executor-enforced constraints installed on the case guarded by `method` — proof each social
/// rule is a real kernel predicate (for the example / audit to print verbatim). Mirrors
/// the crate's `case_constraints`.
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

/// The dispatch method for line `index` in the `bridge` room (the coordinate a driven line
/// presents). A thin re-export of [`choice_method`] pinned to the conversation room.
pub fn line_method(index: usize) -> String {
    choice_method(ROOM_BRIDGE, index)
}

// ── The narrator-voicing hook (a hook, not a hard dep) ────────────────────────────

/// **The world's canonical line for a topic, chosen by the Keeper's committed state.** Mirrors
/// `attested-dm`'s `granted_narration` / `withheld_narration` split: `granted` is `true` when the
/// world would let the line's grant FIRE at the current committed state, and `world_line` is the
/// world's own account. `voiced_prompt` is a seed a narrator brain MAY expand — never a mutation
/// (prose is not power). See [`keeper_line`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeeperLine {
    /// The topic this line answers (`greet` / `history` / `secret` / `cross`).
    pub topic: String,
    /// Whether the world would let this line's grant/topic fire at the current committed state.
    pub granted: bool,
    /// The world's own account of the Keeper's reply (the authoritative narration).
    pub world_line: String,
    /// A prompt a narrator brain may voice/expand into vivid speech (a hook, never a mutation).
    pub voiced_prompt: String,
}

/// **Read the Keeper's committed state and return the WORLD's line for `topic`.** A pure read over
/// the real cell (no turn, no mutation): the executor already decided what the Keeper will do; this
/// only reports the world's account so a narrator ([`crate::narrator`]) can voice it. The narrator
/// MAY call this; nothing in this module depends on the narrator.
///
/// Recognised topics: `greet`, `history`, `secret`, `cross` (an unknown topic yields a silent,
/// non-granting line — the "the NPC has no line on this topic" case `attested-dm` calls
/// `NpcSilent`).
pub fn keeper_line(world: &WorldCell, topic: &str) -> KeeperLine {
    let disposition = world.read_var("disposition");
    let menace = world.read_var("menace");
    let topic_history = world.read_var("topic_history");
    let passage_open = world.read_var("passage_open");

    let (granted, world_line, voiced_prompt) = match topic {
        "greet" => (
            true,
            "The Keeper inclines the lantern a hand's width toward you — an acknowledgement, no more."
                .to_string(),
            "Voice the Lantern-Keeper giving a wary, wordless nod to a stranger's greeting."
                .to_string(),
        ),
        "history" => {
            if menace == 0 && disposition >= HISTORY_DISPOSITION_FLOOR {
                (
                    true,
                    "The Keeper speaks of the lighthouse: how the wick has been kept unbroken for nine hundred nights."
                        .to_string(),
                    "Voice the Keeper, now warmed, recounting the lighthouse's long unbroken vigil."
                        .to_string(),
                )
            } else {
                (
                    false,
                    "The Keeper's jaw sets. That is not a tale for a stranger — or for one who came with a hand on his hilt."
                        .to_string(),
                    "Voice the Keeper refusing the lore — too wary, or affronted by an earlier threat."
                        .to_string(),
                )
            }
        }
        "secret" => {
            if topic_history >= 1 {
                (
                    true,
                    "The Keeper lowers the wick and murmurs the secret: the flame answers only to the honest of heart."
                        .to_string(),
                    "Voice the Keeper confiding the lantern's secret, having already shared the history."
                        .to_string(),
                )
            } else {
                (
                    false,
                    "The Keeper only shakes his head. You have not yet earned the telling that comes before it."
                        .to_string(),
                    "Voice the Keeper deflecting a question asked out of turn, before the history is known."
                        .to_string(),
                )
            }
        }
        "cross" => {
            if passage_open >= 1 {
                (
                    true,
                    "The Keeper fills your flask from the lantern's oil, lifts the chain, and lights your first steps across."
                        .to_string(),
                    "Voice the Keeper, won over, granting passage and a flask of lantern-oil to a friend."
                        .to_string(),
                )
            } else {
                (
                    false,
                    "The chain stays up. However sweetly you ask, the Keeper does not move to lower it."
                        .to_string(),
                    "Voice the Keeper withholding passage — unmoved by words, the way not yet earned."
                        .to_string(),
                )
            }
        }
        other => (
            false,
            format!("The Keeper has no words on that. ({other})"),
            format!("The Lantern-Keeper stays silent on `{other}` — no line for this topic."),
        ),
    };

    KeeperLine {
        topic: topic.to_string(),
        granted,
        world_line,
        voiced_prompt,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use spween_dregg::{
        Driver, Value, VerifyBreak, WorldError, verify, verify_by_replay, verify_chain_linkage,
    };

    // A fresh, wary Keeper for the direct-executor tests (which bypass genesis, so they seed the
    // Keeper's starting regard exactly as the keep/vault tests seed `hp`/`mana_budget`).
    fn wary_keeper(seed: u8) -> WorldCell {
        let mut world = deploy_vigil(seed);
        world.seed_var("disposition", Value::Int(3));
        world
    }

    fn line(scene: &Scene, index: usize) -> spween::Choice {
        crate::choice_at(scene, ROOM_BRIDGE, index)
    }

    /// The social gates lower to REAL executor teeth — a kernel predicate per line, not app
    /// bookkeeping. Reads the installed program back and asserts each tooth is present.
    #[test]
    fn social_gates_lower_to_real_teeth() {
        let story = vigil_compiled();
        let disposition = vigil_slot(&story, "disposition");
        let menace = vigil_slot(&story, "menace");
        let topic_history = vigil_slot(&story, "topic_history");
        let topic_secret = vigil_slot(&story, "topic_secret");

        // The friendly topic is barred below the warmth floor (compiler-emitted FieldGte).
        let hist = case_constraints(&story, &line_method(LN_ASK_HISTORY));
        assert!(
            hist.iter().any(|c| matches!(c,
                StateConstraint::FieldGte { index, value }
                    if *index == disposition && *value == field_from_u64(HISTORY_DISPOSITION_FLOOR))),
            "friendly topic gated FieldGte(disposition, {HISTORY_DISPOSITION_FLOOR}); got {hist:?}"
        );
        assert!(
            hist.iter().any(|c| matches!(c,
                StateConstraint::FieldEquals { index, value }
                    if *index == menace && *value == field_from_u64(0))),
            "friendly topic also gated FieldEquals(menace, 0); got {hist:?}"
        );

        // The goad is the mirror — barred once warmed (FieldLte).
        let goad = case_constraints(&story, &line_method(LN_GOAD));
        assert!(
            goad.iter().any(|c| matches!(c,
                StateConstraint::FieldLte { index, .. } if *index == disposition)),
            "goad gated FieldLte(disposition, ..); got {goad:?}"
        );

        // The locked topic is a BoundedBy on the prerequisite topic.
        let secret = case_constraints(&story, &line_method(LN_ASK_SECRET));
        assert!(
            secret.iter().any(|c| matches!(c,
                StateConstraint::BoundedBy { index, witness_index }
                    if *index == topic_secret && *witness_index == topic_history)),
            "secret topic gated BoundedBy(topic_secret <- topic_history); got {secret:?}"
        );

        // The grant is gated on warmth AND the secret.
        let grant = case_constraints(&story, &line_method(LN_BEG_LEAVE));
        assert!(
            grant.iter().any(|c| matches!(c,
                StateConstraint::FieldGte { index, value }
                    if *index == disposition && *value == field_from_u64(GRANT_DISPOSITION_FLOOR))),
            "grant gated FieldGte(disposition, {GRANT_DISPOSITION_FLOOR}); got {grant:?}"
        );
        assert!(
            grant.iter().any(|c| matches!(c,
                StateConstraint::FieldGte { index, value }
                    if *index == topic_secret && *value == field_from_u64(1))),
            "grant also gated FieldGte(topic_secret, 1); got {grant:?}"
        );
    }

    /// A greeting is a real committed turn that ADVANCES the Keeper's disposition, and the Keeper
    /// REMEMBERS: the raised regard persists across turns (read back off the committed ledger), and
    /// two greetings' receipts chain (`pre == prev.post`).
    #[test]
    fn a_line_advances_disposition_and_the_keeper_remembers() {
        let s = vigil_scene();
        let world = wary_keeper(20);
        assert_eq!(world.read_var("disposition"), 3, "the Keeper begins wary");

        let greet = line(&s, LN_GREET);
        let r1 = world
            .apply_choice(ROOM_BRIDGE, LN_GREET, &greet)
            .expect("a greeting is a real committed turn");
        assert_eq!(
            world.read_var("disposition"),
            4,
            "the greeting warmed the Keeper"
        );

        // The Keeper REMEMBERS across turns: a second, unrelated read still sees the raised regard.
        assert_eq!(
            world.read_var("disposition"),
            4,
            "the raised disposition persists on-ledger between turns"
        );

        let r2 = world
            .apply_choice(ROOM_BRIDGE, LN_GREET, &greet)
            .expect("a second greeting commits");
        assert_eq!(world.read_var("disposition"), 5);
        assert_ne!(
            r1.turn_hash, [0u8; 32],
            "the greeting is a genuine committed turn"
        );
        assert_eq!(
            r2.pre_state_hash, r1.post_state_hash,
            "the dialogue receipts chain (pre == prev.post) — the memory is one serial ledger"
        );
    }

    /// THE HARD GATE (friendly-only line): a WARY Keeper REFUSES the friendly topic — a real
    /// `WorldError::Refused` that commits nothing (anti-ghost: topic still locked). The SAME line
    /// commits once the Keeper is warmed. Non-vacuous: identical line, refused then admitted, one
    /// greeting the only difference.
    #[test]
    fn friendly_line_refused_when_wary_then_unlocks() {
        let s = vigil_scene();
        let world = wary_keeper(21);

        // Wary (disposition 3 < 4): the friendly topic is refused by the executor.
        let ask = line(&s, LN_ASK_HISTORY);
        let refused = world.apply_choice(ROOM_BRIDGE, LN_ASK_HISTORY, &ask);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a wary Keeper refuses the friendly topic, got {refused:?}"
        );
        assert_eq!(
            world.read_var("topic_history"),
            0,
            "anti-ghost: topic still locked"
        );

        // Warm the Keeper with a greeting, then the SAME line commits.
        world
            .apply_choice(ROOM_BRIDGE, LN_GREET, &line(&s, LN_GREET))
            .expect("greeting commits");
        assert_eq!(world.read_var("disposition"), 4);
        world
            .apply_choice(ROOM_BRIDGE, LN_ASK_HISTORY, &ask)
            .expect("the warmed Keeper opens the lore topic");
        assert_eq!(
            world.read_var("topic_history"),
            1,
            "the topic is now unlocked"
        );
    }

    /// THE LOCKED TOPIC (`BoundedBy`): the deep "secret" topic cannot be raised until the "history"
    /// topic is unlocked — a real executor refusal that commits nothing, then commits once the
    /// prerequisite is set. Non-vacuous.
    #[test]
    fn locked_topic_refused_until_prerequisite_unlocked() {
        let s = vigil_scene();
        let world = wary_keeper(22);
        world
            .apply_choice(ROOM_BRIDGE, LN_GREET, &line(&s, LN_GREET))
            .expect("greet"); // disposition 3 -> 4

        // Secret before history: BoundedBy refuses (witness topic_history == 0).
        let secret = line(&s, LN_ASK_SECRET);
        let refused = world.apply_choice(ROOM_BRIDGE, LN_ASK_SECRET, &secret);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "the locked topic is refused before its prerequisite, got {refused:?}"
        );
        assert_eq!(
            world.read_var("topic_secret"),
            0,
            "anti-ghost: secret still locked"
        );

        // Unlock the prerequisite (history), then the SAME secret line commits.
        world
            .apply_choice(ROOM_BRIDGE, LN_ASK_HISTORY, &line(&s, LN_ASK_HISTORY))
            .expect("unlock history");
        assert_eq!(world.read_var("topic_history"), 1);
        world
            .apply_choice(ROOM_BRIDGE, LN_ASK_SECRET, &secret)
            .expect("the secret opens once the history is known");
        assert_eq!(world.read_var("topic_secret"), 1);
    }

    /// THE TWO PATHS GATE EACH OTHER, both directions, non-vacuous. (a) A goaded Keeper's friendly
    /// topic is permanently closed (`FieldEquals(menace, 0)` bites even once warmed). (b) A warmed
    /// Keeper refuses the goad (`FieldLte(disposition, 3)` bites).
    #[test]
    fn hostile_and_friendly_paths_gate_each_other() {
        let s = vigil_scene();

        // (a) Goad first — the friendly topic is closed to you forever after.
        let goaded = wary_keeper(23);
        goaded
            .apply_choice(ROOM_BRIDGE, LN_GOAD, &line(&s, LN_GOAD))
            .expect("goading a wary Keeper (disposition 3 <= 3) commits");
        assert_eq!(
            goaded.read_var("menace"),
            1,
            "the Keeper remembers the threat"
        );
        // Even after a greeting warms disposition, the remembered menace bars the friendly topic.
        goaded
            .apply_choice(ROOM_BRIDGE, LN_GREET, &line(&s, LN_GREET))
            .expect("greet"); // disposition 3 -> 4, over the warmth floor
        let refused = goaded.apply_choice(ROOM_BRIDGE, LN_ASK_HISTORY, &line(&s, LN_ASK_HISTORY));
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a goad, once remembered, permanently closes the friendly topic, got {refused:?}"
        );
        assert_eq!(
            goaded.read_var("topic_history"),
            0,
            "anti-ghost: still closed"
        );

        // (b) Warm first — the goad is now refused (the Keeper won't be threatened).
        let warmed = wary_keeper(24);
        warmed
            .apply_choice(ROOM_BRIDGE, LN_GREET, &line(&s, LN_GREET))
            .expect("greet"); // disposition 3 -> 4
        let refused = warmed.apply_choice(ROOM_BRIDGE, LN_GOAD, &line(&s, LN_GOAD));
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a warmed Keeper refuses the goad, got {refused:?}"
        );
        assert_eq!(
            warmed.read_var("menace"),
            0,
            "anti-ghost: no threat recorded"
        );
    }

    /// THE DIALOGUE GRANT is a real gated effect: begging leave early is REFUSED (no warmth, no
    /// secret) and grants NOTHING; after the Keeper is fully won over the SAME line commits and the
    /// grant (the flask + the opened way) lands as real committed state. Non-vacuous.
    #[test]
    fn dialogue_grant_is_a_real_gated_effect() {
        let s = vigil_scene();
        let world = wary_keeper(25);

        // Beg leave immediately — refused (disposition 3 < 5, no secret). Prose cannot move it.
        let beg = line(&s, LN_BEG_LEAVE);
        let refused = world.apply_choice(ROOM_BRIDGE, LN_BEG_LEAVE, &beg);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "the Keeper's grant is refused before it is earned, got {refused:?}"
        );
        assert_eq!(
            world.read_var("passage_open"),
            0,
            "anti-ghost: the way is not opened"
        );
        assert_eq!(world.read_var("oil_given"), 0, "anti-ghost: no flask given");

        // Win the Keeper over: greet, learn history, learn secret, greet again (disposition 5).
        world
            .apply_choice(ROOM_BRIDGE, LN_GREET, &line(&s, LN_GREET))
            .expect("greet"); // 3->4
        world
            .apply_choice(ROOM_BRIDGE, LN_ASK_HISTORY, &line(&s, LN_ASK_HISTORY))
            .expect("history");
        world
            .apply_choice(ROOM_BRIDGE, LN_ASK_SECRET, &line(&s, LN_ASK_SECRET))
            .expect("secret");
        world
            .apply_choice(ROOM_BRIDGE, LN_GREET, &line(&s, LN_GREET))
            .expect("greet"); // 4->5

        // The SAME grant line now commits — the flask + the opened way are real state.
        world
            .apply_choice(ROOM_BRIDGE, LN_BEG_LEAVE, &beg)
            .expect("the won-over Keeper grants passage");
        assert_eq!(world.read_var("passage_open"), 1, "the way is opened");
        assert_eq!(world.read_var("oil_given"), 1, "the flask is filled");
    }

    /// The narrator-voicing hook reads committed state and returns the world's line: WITHHELD while
    /// unearned, GRANTED once the state gate is satisfied. Mirrors granted/withheld narration —
    /// prose is not power, the hook only reports what the gate already decided.
    #[test]
    fn keeper_line_hook_tracks_committed_state() {
        let s = vigil_scene();
        let world = wary_keeper(26);

        // Wary: the "cross" line is withheld (the way is not open).
        let before = keeper_line(&world, "cross");
        assert!(!before.granted, "the crossing is withheld while unearned");
        assert!(!before.world_line.is_empty() && !before.voiced_prompt.is_empty());

        // The friendly topic reads withheld while wary...
        assert!(
            !keeper_line(&world, "history").granted,
            "history withheld while wary"
        );

        // ...win the Keeper over, and the hook flips to the granted account.
        for ln in [
            LN_GREET,
            LN_ASK_HISTORY,
            LN_ASK_SECRET,
            LN_GREET,
            LN_BEG_LEAVE,
        ] {
            world
                .apply_choice(ROOM_BRIDGE, ln, &line(&s, ln))
                .unwrap_or_else(|e| panic!("winning line {ln} commits: {e}"));
        }
        assert!(
            keeper_line(&world, "history").granted,
            "history now granted"
        );
        assert!(
            keeper_line(&world, "cross").granted,
            "the crossing is now granted"
        );
        // An unknown topic is a silent, non-granting line (the NpcSilent case, re-homed).
        assert!(!keeper_line(&world, "the-weather").granted);
    }

    /// A FULL conversation over the stock runtime is a real receipt chain that re-verifies (chain
    /// linkage + replay), and a FORGED conversation record (a line retconned out of its gate order)
    /// fails replay — the same replay tooth every universe ships.
    #[test]
    fn full_conversation_reverifies_and_a_forged_line_fails() {
        let s = vigil_scene();
        // The winning line of dialogue: greet, learn history, learn secret, greet, beg leave,
        // cross, step across. Driven through the stock Driver (genesis seeds disposition = 3).
        let script = [
            LN_GREET,       // disposition 3 -> 4
            LN_ASK_HISTORY, // topic_history = 1 (disposition >= 4, never goaded)
            LN_ASK_SECRET,  // topic_secret = 1 (history unlocked)
            LN_GREET,       // disposition 4 -> 5
            LN_BEG_LEAVE,   // passage_open = 1, oil_given = 1 (disposition >= 5, secret known)
            LN_CROSS,       // -> across (passage_open >= 1)
        ];

        let mut driver = Driver::start(deploy_vigil(30), &s).expect("start the vigil");
        assert_eq!(
            driver.world().read_var("disposition"),
            3,
            "genesis seeds a wary Keeper"
        );
        for &ln in &script {
            driver
                .advance(ln)
                .unwrap_or_else(|e| panic!("the winning line {ln} lands: {e}"));
        }
        assert_eq!(driver.current_passage().as_deref(), Some(ROOM_ACROSS));
        driver.advance(AC_STEP).expect("step across");
        assert!(
            driver.is_ended(),
            "the Keeper let you cross — the vigil is won"
        );

        // The whole conversation is committed state the Keeper remembers.
        assert_eq!(driver.world().read_var("disposition"), 5);
        assert_eq!(driver.world().read_var("topic_history"), 1);
        assert_eq!(driver.world().read_var("topic_secret"), 1);
        assert_eq!(driver.world().read_var("passage_open"), 1);
        assert_eq!(driver.world().read_var("oil_given"), 1);

        let play = driver.playthrough();
        assert_eq!(play.receipts().len(), 8, "genesis + 7 lines");
        verify_chain_linkage(&play).expect("the conversation receipt chain links");
        verify(deploy_vigil(30), &s, &play).expect("the honest conversation re-verifies by replay");

        // FORGE the record: retcon the FIRST line from a greeting to a goad. Replay reproduces a
        // different state (or the executor refuses a later gated line that the forged prefix no
        // longer earns) — either way the forged conversation fails.
        let mut forged = play.clone();
        forged.steps[0].choice_index = LN_GOAD;
        let out = verify_by_replay(deploy_vigil(30), &s, &forged);
        assert!(
            matches!(
                out,
                Err(VerifyBreak::StateMismatch { .. })
                    | Err(VerifyBreak::RefusedOnReplay { .. })
                    | Err(VerifyBreak::PassageOutOfOrder { .. })
            ),
            "a forged line (a goad retconned in for a greeting) fails replay, got {out:?}"
        );
    }
}
