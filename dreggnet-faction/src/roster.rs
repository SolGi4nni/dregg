//! # Data-driven factions — the roster as DATA, the scene + teeth GENERATED.
//!
//! The [`crate`] root hand-authors ONE faction feud (the Ashenmoor Embers/Tide pair) as an
//! inline [`FEUD`](crate::FEUD) scene. That proved the teeth are real; it did not make factions
//! *authorable*. This module generalizes: a [`Roster`] is a list of [`FactionDef`]s — a faction's
//! display name, its rival, its standing threshold, its trust ceiling — and the SAME scene shape
//! + the SAME executor teeth are GENERATED from that data for any number of factions.
//!
//! Every faction `key` names a stable family of cell slots (the canonical naming the quest /
//! guild / tavern gates read through [`crate::standing`] instead of re-deriving per crate):
//!
//! | slot ([`rep_var`] etc.) | tooth |
//! |-------------------------|-------|
//! | `rep_<key>`             | [`Monotonic`](dregg_app_framework::StateConstraint::Monotonic) — standing is never un-earned |
//! | `<key>_ceiling`         | the rival cap's headroom (a rival pledge decrements it; the pledge reads it as a cross-slot [`FieldLteOther`](dregg_app_framework::StateConstraint::FieldLteOther)) |
//! | `<key>_quest`           | [`WriteOnce`](dregg_app_framework::StateConstraint::WriteOnce) content unlock, gated [`FieldGte`](dregg_app_framework::StateConstraint::FieldGte)`(rep, threshold)` + never-betrayed |
//! | `<key>_betrayed`        | [`WriteOnce`](dregg_app_framework::StateConstraint::WriteOnce) betrayal seal |
//!
//! The generated program is deployed on the SAME [`WorldCell`] as the hand-authored feud, so a
//! data-driven roster's standing is exactly as executor-refereed as the inline example: you
//! cannot fake standing, content stays gated, a betrayal permanently seals — for N factions, from
//! data.

use std::sync::Arc;

use dregg_app_framework::{StateConstraint, field_from_u64};
use serde::{Deserialize, Serialize};
use spween::{Scene, Value};
use spween_dregg::{CompiledStory, WorldCell, choice_method, compile_scene, parse};

use crate::{ROOM_HALL, augment_case, faction_slot};

// ── The canonical slot naming (the SHARED contract the reader crates read through) ──────────

/// The reputation slot for `key` — `rep_<key>`. A `Monotonic` ratchet; a pledge raises it.
pub fn rep_var(key: &str) -> String {
    format!("rep_{key}")
}
/// The trust-ceiling headroom slot for `key` — `<key>_ceiling`. A rival pledge decrements it; the
/// faction's own pledge is gated `rep_<key> < "$<key>_ceiling"` (the cross-slot cap).
pub fn ceiling_var(key: &str) -> String {
    format!("{key}_ceiling")
}
/// The content-unlock slot for `key` — `<key>_quest`. A `WriteOnce` flag the gated trial sets.
pub fn quest_var(key: &str) -> String {
    format!("{key}_quest")
}
/// The betrayal-seal slot for `key` — `<key>_betrayed`. A `WriteOnce` flag; once set it seals the
/// faction's content forever.
pub fn betrayed_var(key: &str) -> String {
    format!("{key}_betrayed")
}
/// The gated REGION room reached once the faction's content unlocks — `<key>_region`.
pub fn region_room(key: &str) -> String {
    format!("{key}_region")
}

// ── The data model ──────────────────────────────────────────────────────────────────────────

/// **One faction, as data.** The display name + the numeric bars the generated teeth enforce.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactionDef {
    /// The stable slug (`embers`) — names the slot family (`rep_embers`, `embers_ceiling`, …) and
    /// the region room. Must be a valid identifier fragment (letters / digits / `_`).
    pub key: String,
    /// The display name (`the Embers`) — shown in prose + the standing surface.
    pub name: String,
    /// A one-line region blurb (rendered in the faction's gated region room).
    pub blurb: String,
    /// The rival faction's `key`: a pledge to THIS faction decrements the rival's `<rival>_ceiling`
    /// (so pledging one caps the other). `None` = an unaligned faction with no rival cap.
    pub rival: Option<String>,
    /// The standing a pledge must reach before the faction's content unlocks (`rep >= threshold`).
    pub threshold: u64,
    /// The full trust a faction extends before a rival's pull caps it (the ceiling's start value).
    pub trust_ceiling: u64,
}

impl FactionDef {
    /// A conventional faction: `threshold` [`REP_THRESHOLD`](crate::REP_THRESHOLD), `trust_ceiling`
    /// [`TRUST_CEILING`](crate::TRUST_CEILING), rival `rival`.
    pub fn new(
        key: impl Into<String>,
        name: impl Into<String>,
        blurb: impl Into<String>,
        rival: Option<&str>,
    ) -> Self {
        FactionDef {
            key: key.into(),
            name: name.into(),
            blurb: blurb.into(),
            rival: rival.map(str::to_string),
            threshold: crate::REP_THRESHOLD,
            trust_ceiling: crate::TRUST_CEILING,
        }
    }
}

/// The hall line coordinates for one faction (the driver + verifier address a faction move by
/// these). Six self-looping hall choices per faction, in a contiguous block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FactionLines {
    /// Pledge — raises `rep_<key>` (`Monotonic`), drops the rival ceiling, gated on the own ceiling.
    pub pledge: usize,
    /// Undertake the trial — the gated content (`FieldGte(rep, threshold)` + never-betrayed, sets
    /// the `WriteOnce` unlock).
    pub trial: usize,
    /// Betray — sets the `WriteOnce` betrayal seal.
    pub betray: usize,
    /// Renounce — an attempted `Monotonic` write-down of `rep_<key>` (refused once standing is held).
    pub renounce: usize,
    /// Recant — an attempted un-set of the betrayal (refused by `WriteOnce`).
    pub recant: usize,
    /// Enter the faction's gated region (`FieldGte(<key>_quest, 1)`).
    pub enter: usize,
}

/// The number of hall choices generated per faction.
pub const LINES_PER_FACTION: usize = 6;

/// **A whole faction roster, as data.** Generates the feud scene + the executor teeth for any
/// number of factions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Roster {
    /// The scene id (stable — the deterministic world-cell identity derives from it).
    pub id: String,
    /// The scene title.
    pub title: String,
    /// A one-line intro shown in the faction hall.
    pub intro: String,
    /// The factions, in hall-line order.
    pub factions: Vec<FactionDef>,
}

impl Roster {
    /// **The canonical Ashenmoor roster** — the same Embers/Tide rival pair the inline
    /// [`FEUD`](crate::FEUD) hand-authors, now expressed as data. Proof the generator subsumes the
    /// hand-authored example: the generated teeth are identical in shape.
    pub fn ashenmoor() -> Self {
        Roster {
            id: "ashenmoor-feud-roster".to_string(),
            title: "The Feud at the Ashenmoor Gate".to_string(),
            intro: "Two banners hang over the Ashenmoor gate, and neither warden loves the other."
                .to_string(),
            factions: vec![
                FactionDef::new(
                    "embers",
                    "the Embers",
                    "The beacon-keepers part for you; the eternal flame names you kin.",
                    Some("tide"),
                ),
                FactionDef::new(
                    "tide",
                    "the Tide",
                    "The grey wave draws back from a stair going down into the drowned hall.",
                    Some("embers"),
                ),
            ],
        }
    }

    /// Find a faction by `key`.
    pub fn faction(&self, key: &str) -> Option<&FactionDef> {
        self.factions.iter().find(|f| f.key == key)
    }

    /// The hall line block for the faction at position `i`.
    pub fn lines_at(&self, i: usize) -> FactionLines {
        let base = i * LINES_PER_FACTION;
        FactionLines {
            pledge: base,
            trial: base + 1,
            betray: base + 2,
            renounce: base + 3,
            recant: base + 4,
            enter: base + 5,
        }
    }

    /// The hall line block for the faction named `key` (panics if absent).
    pub fn lines(&self, key: &str) -> FactionLines {
        let i = self
            .factions
            .iter()
            .position(|f| f.key == key)
            .unwrap_or_else(|| panic!("faction `{key}` is in the roster"));
        self.lines_at(i)
    }

    /// **Validate the roster is well-formed** — non-empty, unique keys, every named rival present,
    /// keys are identifier-safe. A generated scene from an invalid roster would mis-compile; this
    /// catches it with a message instead.
    pub fn validate(&self) -> Result<(), String> {
        if self.factions.is_empty() {
            return Err("a roster needs at least one faction".to_string());
        }
        for f in &self.factions {
            if f.key.is_empty() || !f.key.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                return Err(format!("faction key `{}` must be identifier-safe", f.key));
            }
            if self.factions.iter().filter(|g| g.key == f.key).count() > 1 {
                return Err(format!("faction key `{}` is not unique", f.key));
            }
            if let Some(rival) = &f.rival {
                if self.faction(rival).is_none() {
                    return Err(format!(
                        "faction `{}` names a rival `{rival}` not in the roster",
                        f.key
                    ));
                }
            }
        }
        Ok(())
    }

    /// **Generate the feud scene text** — the whole roster as one spween scene. Each faction
    /// contributes six self-looping hall choices (pledge / trial / betray / renounce / recant /
    /// enter-region) + a gated region room. The pledge condition (`rep < "$ceiling"`), the trial
    /// gate (`rep >= threshold`), and the region entry (`quest >= 1`) are conditions the compiler
    /// lowers; [`Roster::compile`] augments the shapes the v0 compiler does not emit.
    pub fn scene_text(&self) -> String {
        let mut s = String::new();
        s.push_str("---\n");
        s.push_str(&format!("id: {}\n", self.id));
        s.push_str(&format!("title: {}\n", self.title));
        s.push_str("weight: 1\n");
        s.push_str("---\n\n");

        s.push_str(&format!("=== {ROOM_HALL}\n\n"));
        // Seed each ceiling to its full trust (mirrors the inline FEUD's top-of-hall effects;
        // `Roster::deploy` also seeds them directly).
        for f in &self.factions {
            s.push_str(&format!(
                "~ {} = {}\n",
                ceiling_var(&f.key),
                f.trust_ceiling
            ));
        }
        s.push('\n');
        s.push_str(&self.intro);
        s.push_str("\n\n");

        for f in &self.factions {
            let key = &f.key;
            let name = &f.name;

            // Pledge — gated on the OWN ceiling (lowers to FieldLteOther); raises rep + drops the
            // rival's ceiling.
            s.push_str(&format!(
                "* [Pledge your arm to {name}] {{ {} < \"${}\" }}\n",
                rep_var(key),
                ceiling_var(key)
            ));
            s.push_str(&format!("  ~ {} += 1\n", rep_var(key)));
            if let Some(rival) = &f.rival {
                s.push_str(&format!("  ~ {} -= 1\n", ceiling_var(rival)));
            }
            s.push_str(&format!("  -> {ROOM_HALL}\n\n"));

            // Trial — the gated content.
            s.push_str(&format!(
                "* [Undertake the {name} trial] {{ {} >= {} }}\n",
                rep_var(key),
                f.threshold
            ));
            s.push_str(&format!("  ~ {} = 1\n", quest_var(key)));
            s.push_str(&format!("  -> {ROOM_HALL}\n\n"));

            // Betray — the seal.
            s.push_str(&format!("* [Betray {name}]\n"));
            s.push_str(&format!("  ~ {} = 1\n", betrayed_var(key)));
            s.push_str(&format!("  -> {ROOM_HALL}\n\n"));

            // Renounce — the write-down.
            s.push_str(&format!("* [Renounce your {name} standing]\n"));
            s.push_str(&format!("  ~ {} = 0\n", rep_var(key)));
            s.push_str(&format!("  -> {ROOM_HALL}\n\n"));

            // Recant — the un-set of the betrayal.
            s.push_str(&format!("* [Recant the betrayal of {name}]\n"));
            s.push_str(&format!("  ~ {} = 0\n", betrayed_var(key)));
            s.push_str(&format!("  -> {ROOM_HALL}\n\n"));

            // Enter the gated region.
            s.push_str(&format!(
                "* [Enter the {name} sanctum] {{ {} >= 1 }}\n",
                quest_var(key)
            ));
            s.push_str(&format!("  -> {}\n\n", region_room(key)));
        }

        // The gated region rooms.
        for f in &self.factions {
            s.push_str(&format!("=== {}\n\n", region_room(&f.key)));
            s.push_str(&f.blurb);
            s.push_str("\n\n");
            s.push_str(&format!("* [Enter the halls of {}]\n", f.name));
            s.push_str("  -> END\n\n");
        }

        s
    }

    /// Parse the generated scene.
    pub fn scene(&self) -> Scene {
        parse(&self.scene_text(), &format!("{}.scene", self.id))
            .expect("the generated scene parses")
    }

    /// **Compile the roster AND augment its program with the faction teeth** — the data-driven
    /// twin of [`crate::faction_compiled`]. Per faction: `Monotonic` on the pledge + renounce, the
    /// `FieldEquals(betrayed, 0)` seal + `WriteOnce(quest)` on the trial, and `WriteOnce(betrayed)`
    /// on the betray + recant. The threshold gate, the region entry, and the cross-slot ceiling cap
    /// are already compiler-emitted from the generated conditions.
    pub fn compile(&self) -> CompiledStory {
        self.validate().expect("the roster is well-formed");
        let mut story = compile_scene(&self.scene()).expect("the generated roster compiles");

        for (i, f) in self.factions.iter().enumerate() {
            let lines = self.lines_at(i);
            let rep = faction_slot(&story, &rep_var(&f.key));
            let quest = faction_slot(&story, &quest_var(&f.key));
            let betrayed = faction_slot(&story, &betrayed_var(&f.key));
            let zero = field_from_u64(0);

            // The rep ratchet — Monotonic on every case that writes rep.
            augment_case(
                &mut story.program,
                &choice_method(ROOM_HALL, lines.pledge),
                vec![StateConstraint::Monotonic { index: rep }],
            );
            augment_case(
                &mut story.program,
                &choice_method(ROOM_HALL, lines.renounce),
                vec![StateConstraint::Monotonic { index: rep }],
            );

            // The trial — a betrayal seal + a WriteOnce unlock (the threshold gate is compiled).
            augment_case(
                &mut story.program,
                &choice_method(ROOM_HALL, lines.trial),
                vec![
                    StateConstraint::FieldEquals {
                        index: betrayed,
                        value: zero,
                    },
                    StateConstraint::WriteOnce { index: quest },
                ],
            );

            // The betrayal + recant — a WriteOnce seal, un-reopenable.
            augment_case(
                &mut story.program,
                &choice_method(ROOM_HALL, lines.betray),
                vec![StateConstraint::WriteOnce { index: betrayed }],
            );
            augment_case(
                &mut story.program,
                &choice_method(ROOM_HALL, lines.recant),
                vec![StateConstraint::WriteOnce { index: betrayed }],
            );
        }

        story
    }

    /// **Deploy the roster as a real world-cell**, the faction teeth installed as executor
    /// predicates. Deterministic in `seed`. Each faction's ceiling is seeded to its full trust
    /// (mirrors [`crate::deploy_feud`]); everything else starts at zero — you arrive unaligned.
    pub fn deploy(&self, seed: u8) -> WorldCell {
        let mut world =
            WorldCell::deploy_compiled(Arc::new(self.compile()), seed).expect("the roster deploys");
        for f in &self.factions {
            world.seed_var(&ceiling_var(&f.key), Value::Int(f.trust_ceiling as i64));
        }
        world
    }
}
