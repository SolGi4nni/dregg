//! # `descent_card` — the SHARED run's picture: the shaft as it stood when the run ended.
//!
//! `/descent/native/run/{id}` is the artifact a stranger actually meets. It used to say
//! **`Banked relics: 3`** — a number with no story attached: not *which* relics, not how deep the
//! player got, not what they were still carrying when the light went out. This module paints the
//! run instead.
//!
//! ## The picture is the LIVE surface's picture
//!
//! The play surface (`dreggnet_offerings::native_descent::descent_map`, mirrored in the browser by
//! `descent_play`'s `buildMap`) draws the dungeon as a coordinate board: `marker · way · guardian`
//! then **one column per relic**, rows floors `1..=FLOORS` then the pack row `@` then the vault row
//! `$`. A relic's column is FIXED for the whole run, so you watch it travel out of its floor, into
//! the pack (still losable), and into the vault (yours). The run-card paints the SAME board with
//! the SAME glyphs in the SAME column order — a player who watched their run happen recognises the
//! shape of it on the share link.
//!
//! Three things are reused rather than re-invented:
//!
//! * the numbers are the game's own re-exported Lean-sourced constants
//!   ([`LIGHT_BREATH`], [`DUNGEON_FLOORS`], [`DUNGEON_RELICS`], [`CUSTODY_CARRIED`],
//!   [`CUSTODY_BANKED`]) and the **day's own drawn map** ([`DayWorld`], resolved from the record's
//!   committed day-seed) — nothing here mirrors a world number;
//! * the plain-text board is [`deos_view::coordgrid_text`], the ONE board projection every text
//!   channel already uses, so the copyable card is the same board Discord/Telegram paint;
//! * the light clock is [`deos_view::meter_bar`], the ONE meter projection.
//!
//! The GLYPHS are the one genuine mirror: `native_descent`'s table is private to that crate.
//! `tests/descent_run_card.rs` pins each of them against the served play controller's own
//! declaration, so the card and the live surface cannot drift into two different alphabets in
//! silence. (The standing request to `dreggnet-offerings` is to export that table; until then, the
//! test is the weld.)
//!
//! ## What the card claims
//!
//! NOTHING about legality. Every cell is read off the **replayed** final [`PortableSim`] — the
//! post-state the server's own exact re-execution produced, not the submitted one — and off the
//! day's drawn [`DayWorld`]. No rule is re-derived here: this module cannot make an illegal run
//! look legal, because it never decides anything. It is the picture; the verdict panel beside it is
//! the proof.
//!
//! ## The loss beat
//!
//! `flee` banks the whole pack, so a run that ENDED has an empty pack row. A run whose light died
//! never fled: its relics are frozen in the `@` row forever, and the vault is empty. That is the
//! game's strongest beat and the card paints it as a beat — the pack row struck through in red,
//! the vault row's emptiness said out loud — instead of reporting `Banked relics: 0`.

use deos_view::{CoordCell, METER_TEXT_WIDTH, coordgrid_text, meter_bar};
use dreggnet_offerings::native_descent::{
    CARRY_CAP, CUSTODY_BANKED, CUSTODY_CARRIED, DUNGEON_FLOORS, DUNGEON_RELICS, LIGHT_BREATH,
};
use dreggnet_offerings::native_descent_wire::PortableSim;
use dungeon_on_dregg::descent::DayWorld;

use crate::esc;

// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE ALPHABET — mirrored from `native_descent`'s private glyph table, PINNED by
// `tests/descent_run_card.rs` against the served play controller's own declarations.
// ═══════════════════════════════════════════════════════════════════════════════════════════

const GLYPH_EMPTY: &str = "·";
/// The floor the run ended standing on.
const GLYPH_YOU: &str = ">";
const GLYPH_WAY_OPEN: &str = "/";
const GLYPH_WAY_SHUT: &str = "#";
const GLYPH_GUARDIAN: &str = "G";
const GLYPH_GUARDIAN_SLAIN: &str = "x";
const GLYPH_CROWN: &str = "C";
const GLYPH_KEY: &str = "k";
const GLYPH_TREASURE: &str = "*";
/// The pack row — what was ON the player. On a settled run, empty. On a dead run, the loss.
const GLYPH_PACK: &str = "@";
/// The vault row — what a proved exit made theirs.
const GLYPH_VAULT: &str = "$";

/// `marker + way + guardian + one column PER RELIC` — the live board's width, unchanged.
const MAP_COLS: usize = 3 + DUNGEON_RELICS;

/// The glyph a relic paints in its fixed column (its KIND).
fn relic_glyph(relic: usize) -> &'static str {
    match relic {
        0 => GLYPH_CROWN,
        1..=3 => GLYPH_KEY,
        _ => GLYPH_TREASURE,
    }
}

/// The semantic palette tag a relic's cell paints in — the live board's tags.
fn relic_tag(relic: usize) -> &'static str {
    match relic {
        0 => "accent",
        1..=3 => "warn",
        _ => "good",
    }
}

/// A relic named as a NOUN (the live surface names it as an action — "Take the …" — because there
/// it is a button; here it is a thing that was won or lost).
fn relic_name(relic: usize) -> String {
    match relic {
        0 => "the Crown of the Deep".to_string(),
        1..=3 => format!("the way-{} key", relic + 1),
        _ => format!("treasure {}", relic - 3),
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE ENDING — one word, and what it means.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// How the run ended. The words are the LIVE surface's words (`native_descent::descent_status` /
/// the play page's `standing()`), so a player reads the same verdict on the card they read in the
/// tab — with `CROWNED` as the refinement of a settled exit that carried relic 0 out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Ending {
    /// A proved exit, with the Crown of the Deep in it.
    Crowned,
    /// A proved exit. Everything in the pack became theirs.
    Banked,
    /// The light ran out before an exit. Every verb costs at least one light, so a run that cannot
    /// pay one can never move again — whatever was in the pack is frozen there.
    LightDied,
    /// An exact prefix: the run has light left and simply has not ended.
    Delving,
}

impl Ending {
    /// The one-word stamp.
    pub(crate) fn word(self) -> &'static str {
        match self {
            Ending::Crowned => "CROWNED",
            Ending::Banked => "BANKED",
            Ending::LightDied => "THE LIGHT IS DEAD",
            Ending::Delving => "DELVING",
        }
    }

    /// The semantic palette tag (`good` / `bad` / `warn`).
    pub(crate) fn tone(self) -> &'static str {
        match self {
            Ending::Crowned | Ending::Banked => "good",
            Ending::LightDied => "bad",
            Ending::Delving => "warn",
        }
    }

    fn settled(self) -> bool {
        matches!(self, Ending::Crowned | Ending::Banked)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE STORY — the whole run, read off the REPLAYED final state.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// One run's picture: the day's drawn map plus the replayed final state.
///
/// Built ONLY from material the server's own exact re-execution produced. `world` is the day's
/// Lean-emitted draw (which relic was minted where, how tough each floor's guardian is), resolved
/// from the record's committed day-seed — so a beacon day's card shows the beacon day's dungeon
/// rather than day 0's shipped one.
pub(crate) struct RunStory {
    state: PortableSim,
    world: DayWorld,
    ending: Ending,
}

/// A cell's story-flavour, on top of the live board's palette tag: what makes the run-card's board
/// different from the live one is exactly which cells are FINAL.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Flavour {
    Plain,
    /// The floor the run ended on.
    Here,
    /// In the vault: a proved exit made it theirs.
    Banked,
    /// In the pack when the light died: never theirs, and never will be.
    Lost,
    /// In the pack of a run that has not ended. Nothing is theirs until a proved exit banks it.
    AtRisk,
    /// Still lying in the shaft on a floor the run never stood on.
    Unreached,
}

struct Cell {
    glyph: String,
    tag: &'static str,
    flavour: Flavour,
}

impl Cell {
    fn new(glyph: &str, tag: &'static str, flavour: Flavour) -> Self {
        Cell {
            glyph: glyph.to_string(),
            tag,
            flavour,
        }
    }

    fn empty() -> Self {
        Cell::new(GLYPH_EMPTY, "muted", Flavour::Plain)
    }

    /// The shared board projection's cell. `highlight` stays FALSE on every run-card cell: the
    /// text projection brackets a highlighted cell and the live legend reads that bracket as "you
    /// may act on it NOW". Nothing on a finished run is actionable, and re-pointing the bracket at
    /// a second meaning would make one glyph mean two things across two surfaces.
    fn as_coord_cell(&self) -> CoordCell {
        CoordCell {
            glyph: self.glyph.clone(),
            tag: self.tag.to_string(),
            turn: String::new(),
            arg: 0,
            highlight: false,
        }
    }
}

impl RunStory {
    /// Read a run's story off its replayed final state and the day's drawn map.
    ///
    /// `crowned` is the settlement's own committed bit; it is used only to refine a settled run's
    /// word, never to claim a run settled.
    pub(crate) fn new(state: PortableSim, world: DayWorld, crowned: bool) -> Self {
        let ending = if state.fate != 0 {
            if crowned || custody_of(&state, 0) == Some(CUSTODY_BANKED) {
                Ending::Crowned
            } else {
                Ending::Banked
            }
        } else if state.spent + 1 > LIGHT_BREATH {
            // Every verb costs at least one light: a run that cannot pay one can never move again.
            Ending::LightDied
        } else {
            Ending::Delving
        };
        RunStory {
            state,
            world,
            ending,
        }
    }

    pub(crate) fn ending(&self) -> Ending {
        self.ending
    }

    /// Relics a proved exit made theirs.
    pub(crate) fn banked(&self) -> Vec<usize> {
        self.relics_in(CUSTODY_BANKED)
    }

    /// Relics still in the pack. On a settled run this is EMPTY by construction (`flee` banks the
    /// pack); on a dead run it is the loss.
    pub(crate) fn in_pack(&self) -> Vec<usize> {
        self.relics_in(CUSTODY_CARRIED)
    }

    /// Relics in the pack when the light died — gone, and the reason the card exists.
    pub(crate) fn lost(&self) -> Vec<usize> {
        if self.ending == Ending::LightDied {
            self.in_pack()
        } else {
            Vec::new()
        }
    }

    /// **Relics still lying in the shaft** — never picked up at all.
    ///
    /// This is the loss EVERY run takes, and the one the game is actually built around: carrying
    /// rights attenuate with depth (`pack + depth <= CAP`), so a run standing on floor 4 can hold
    /// at most `CAP - 4` relics. Reaching the crown therefore means walking past treasure, and the
    /// card says which treasure.
    pub(crate) fn left_in_the_dark(&self) -> Vec<usize> {
        (0..DUNGEON_RELICS)
            .filter(|&relic| {
                custody_of(&self.state, relic)
                    .is_some_and(|custody| (1..=DUNGEON_FLOORS).contains(&custody))
            })
            .collect()
    }

    /// The deepest floor the run stood on. `delve` is the only depth change and it only goes down,
    /// so the final depth IS the deepest reached.
    pub(crate) fn depth(&self) -> u64 {
        self.state.depth
    }

    pub(crate) fn light_spent(&self) -> u64 {
        self.state.spent.min(LIGHT_BREATH)
    }

    pub(crate) fn light_left(&self) -> u64 {
        LIGHT_BREATH.saturating_sub(self.state.spent)
    }

    fn relics_in(&self, custody: u64) -> Vec<usize> {
        (0..DUNGEON_RELICS)
            .filter(|&relic| custody_of(&self.state, relic) == Some(custody))
            .collect()
    }

    /// **The board.** Floors `1..=FLOORS`, then the pack row, then the vault row — the live
    /// surface's rows, columns and glyphs, with the run's ending decided per cell.
    fn board(&self) -> Vec<Cell> {
        let mut cells = Vec::with_capacity(MAP_COLS * (DUNGEON_FLOORS as usize + 2));
        let depth = self.state.depth;

        for floor in 1..=DUNGEON_FLOORS {
            let ended_here = depth == floor;
            let unreached = floor > depth;

            // The row marker: the floor's number, or `>` on the floor the run ended standing on.
            let marker = if ended_here {
                GLYPH_YOU.to_string()
            } else {
                floor.to_string()
            };
            cells.push(Cell::new(
                &marker,
                if ended_here { "accent" } else { "muted" },
                if ended_here {
                    Flavour::Here
                } else if unreached {
                    Flavour::Unreached
                } else {
                    Flavour::Plain
                },
            ));

            // The way INTO this floor, as it stood at the end. Floor 1 is the mouth (always open);
            // a deeper way opens only once its key-relic was EXERCISED, so a shut way this deep is
            // a key the run never spent.
            let open = way_open(&self.state, floor);
            cells.push(Cell::new(
                if open { GLYPH_WAY_OPEN } else { GLYPH_WAY_SHUT },
                if open { "good" } else { "bad" },
                Flavour::Plain,
            ));

            // The guardian. Wounds are per-standing-floor, so only the guardian the run ENDED
            // facing can read as slain — exactly the live board's rule, on the day's own vitality
            // table rather than day 0's.
            let slain_here = ended_here && self.state.wounds >= self.world.guard_hp(floor);
            cells.push(Cell::new(
                if slain_here {
                    GLYPH_GUARDIAN_SLAIN
                } else {
                    GLYPH_GUARDIAN
                },
                match (ended_here, slain_here) {
                    (true, true) => "good",
                    (true, false) => "bad",
                    _ => "muted",
                },
                Flavour::Plain,
            ));

            // One column per relic: what was still LYING on this floor when it ended.
            for relic in 0..DUNGEON_RELICS {
                if custody_of(&self.state, relic) == Some(floor) {
                    cells.push(Cell::new(
                        relic_glyph(relic),
                        relic_tag(relic),
                        if unreached {
                            Flavour::Unreached
                        } else {
                            Flavour::Plain
                        },
                    ));
                } else {
                    cells.push(Cell::empty());
                }
            }
        }

        // The pack row. `flee` banks the whole pack, so on a SETTLED run it is empty by
        // construction; anything still here is a relic that never became anyone's — lost outright
        // if the light died, at risk while the run is unfinished.
        let carrying = !self.in_pack().is_empty();
        let (pack_flavour, pack_tag) = match (self.ending, carrying) {
            (Ending::LightDied, true) => (Flavour::Lost, "bad"),
            (Ending::Delving, true) => (Flavour::AtRisk, "warn"),
            _ => (Flavour::Plain, "muted"),
        };
        cells.push(Cell::new(GLYPH_PACK, pack_tag, pack_flavour));
        cells.push(Cell::empty());
        cells.push(Cell::empty());
        for relic in 0..DUNGEON_RELICS {
            if custody_of(&self.state, relic) == Some(CUSTODY_CARRIED) {
                cells.push(Cell::new(
                    relic_glyph(relic),
                    match pack_flavour {
                        Flavour::Lost => "bad",
                        Flavour::AtRisk => "warn",
                        _ => relic_tag(relic),
                    },
                    pack_flavour,
                ));
            } else {
                cells.push(Cell::empty());
            }
        }

        // The vault row — what came out.
        let any_banked = !self.banked().is_empty();
        cells.push(Cell::new(
            GLYPH_VAULT,
            if any_banked { "good" } else { "muted" },
            Flavour::Plain,
        ));
        cells.push(Cell::empty());
        cells.push(Cell::empty());
        for relic in 0..DUNGEON_RELICS {
            if custody_of(&self.state, relic) == Some(CUSTODY_BANKED) {
                cells.push(Cell::new(relic_glyph(relic), "good", Flavour::Banked));
            } else {
                cells.push(Cell::empty());
            }
        }

        cells
    }

    /// The per-row caption the text board carries — what makes an `@` row of glyphs read as a loss
    /// rather than as data.
    fn row_labels(&self) -> Vec<String> {
        let depth = self.state.depth;
        let mut labels: Vec<String> = (1..=DUNGEON_FLOORS)
            .map(|floor| match floor.cmp(&depth) {
                std::cmp::Ordering::Equal => {
                    format!("floor {floor} — the run ended here")
                }
                std::cmp::Ordering::Greater => format!("floor {floor} — never reached"),
                std::cmp::Ordering::Less => format!("floor {floor}"),
            })
            .collect();

        let pack = self.in_pack();
        labels.push(match (self.ending, pack.len()) {
            (Ending::LightDied, 0) => "pack — empty when the light died".to_string(),
            (Ending::LightDied, n) => format!(
                "LOST — the light died with {n} relic{} still on them",
                plural(n)
            ),
            (_, 0) if self.ending.settled() => {
                "pack — emptied into the vault by the exit".to_string()
            }
            (_, 0) => "pack — empty".to_string(),
            (_, n) => format!("pack — {n} relic{} carried, still losable", plural(n)),
        });

        let banked = self.banked();
        labels.push(match banked.len() {
            0 if self.ending.settled() => "banked — the exit carried nothing out".to_string(),
            0 => "banked — nothing; no proved exit was ever made".to_string(),
            n => format!("banked — {n} relic{} came out", plural(n)),
        });
        labels
    }

    /// **The copyable card.** The board is [`coordgrid_text`] verbatim — the same projection the
    /// Discord embed and the Telegram message paint — with a caption welded to each row, and the
    /// light clock as [`meter_bar`]. This is the thing a player pastes into a chat.
    pub(crate) fn text_card(&self, actor: &str, day_key: &str) -> String {
        let cells: Vec<CoordCell> = self.board().iter().map(Cell::as_coord_cell).collect();
        let board = coordgrid_text(MAP_COLS, &cells);
        let labels = self.row_labels();
        // `{:width$}` pads by CHARS, and the board is full of multi-byte `·` — measuring in bytes
        // would ragged every caption by one column per empty cell.
        let width = board
            .lines()
            .map(|line| line.chars().count())
            .max()
            .unwrap_or(0);

        let mut out = String::new();
        out.push_str(&format!(
            "{} — {} · {}\n",
            self.ending.word(),
            actor,
            day_key
        ));
        out.push_str(&format!("{}\n\n", self.headline()));
        for (line, label) in board.lines().zip(labels.iter()) {
            out.push_str(&format!("{line:width$}   {label}\n"));
        }
        out.push_str(&format!(
            "\nlight  {}  {} left of {LIGHT_BREATH} ({} spent)\ndepth  {} of {DUNGEON_FLOORS}\n",
            meter_bar(self.light_left(), LIGHT_BREATH, METER_TEXT_WIDTH),
            self.light_left(),
            self.light_spent(),
            self.depth(),
        ));
        let left = self.left_in_the_dark();
        if !left.is_empty() {
            out.push_str(&format!("\nleft in the dark: {}\n", name_list(&left)));
        }
        out.push_str(&format!("\n{}\n", legend_line()));
        out
    }

    /// **The one-sentence story** — the deck, and the social-preview description. It leads with
    /// what happened to the relics, because that is what a stranger is being invited to risk.
    pub(crate) fn headline(&self) -> String {
        let banked = self.banked();
        let lost = self.lost();
        let left = self.left_in_the_dark();
        let and_left = if left.is_empty() {
            " Nothing was left behind.".to_string()
        } else {
            format!(
                " {} relic{} left in the dark.",
                left.len(),
                plural(left.len())
            )
        };
        match self.ending {
            Ending::Crowned => format!(
                "The Crown of the Deep came out of floor {} — {} relic{} banked, {} light left of {LIGHT_BREATH}.{and_left}",
                self.depth(),
                banked.len(),
                plural(banked.len()),
                self.light_left(),
            ),
            Ending::Banked if banked.is_empty() => format!(
                "Climbed out of floor {} empty-handed with {} light left of {LIGHT_BREATH}.{and_left}",
                self.depth(),
                self.light_left(),
            ),
            Ending::Banked => format!(
                "{} relic{} carried out of floor {} on a proved exit, with {} light left of {LIGHT_BREATH}.{and_left}",
                banked.len(),
                plural(banked.len()),
                self.depth(),
                self.light_left(),
            ),
            Ending::LightDied if lost.is_empty() => format!(
                "The light burned out on floor {} with an empty pack. All {LIGHT_BREATH} spent, nothing banked.{and_left}",
                self.depth(),
            ),
            Ending::LightDied => format!(
                "The light burned out on floor {} carrying {} — never banked, never theirs.{and_left}",
                self.depth(),
                name_list(&lost),
            ),
            Ending::Delving => format!(
                "Still on floor {} of {DUNGEON_FLOORS} with {} light left of {LIGHT_BREATH} and {} relic{} riding unbanked in the pack — this run has not ended.",
                self.depth(),
                self.light_left(),
                self.in_pack().len(),
                plural(self.in_pack().len()),
            ),
        }
    }

    /// **The card, as HTML.** One dark plaque: the verdict stamped big enough to read in a
    /// thumbnail, the shaft under it, the run's three numbers beside it, and the loss said out
    /// loud when there is one.
    pub(crate) fn html(&self, actor: &str, day_key: &str, seed_tag: &str) -> String {
        let cells = self.board();
        let mut grid = String::new();
        for cell in &cells {
            let flavour = match cell.flavour {
                Flavour::Plain => "",
                Flavour::Here => " here",
                Flavour::Banked => " banked",
                Flavour::Lost => " lost",
                Flavour::AtRisk => " at-risk",
                Flavour::Unreached => " unreached",
            };
            grid.push_str(&format!(
                "<span class=\"rc-cell tag-{tag}{flavour}\">{glyph}</span>",
                tag = cell.tag,
                flavour = flavour,
                glyph = esc(&cell.glyph),
            ));
        }

        let lost = self.lost();
        let banked = self.banked();
        let pack = self.in_pack();
        let left = self.left_in_the_dark();

        // THE LOSS, said out loud. Two kinds, and they are different griefs: what was ON them and
        // never became theirs, and what they had to walk past to carry what they did.
        let loss_note = if !lost.is_empty() {
            format!(
                "<p class=\"rc-loss\"><strong>{n} relic{s} died in the dark.</strong> {names} \
                 {was} in the pack when the light went out. Nothing is yours until a proved exit \
                 banks it — and there was no light left to buy one.</p>",
                n = lost.len(),
                s = plural(lost.len()),
                names = esc(&sentence_case(&name_list(&lost))),
                was = if lost.len() == 1 { "was" } else { "were" },
            )
        } else if self.ending == Ending::Delving && !pack.is_empty() {
            format!(
                "<p class=\"rc-risk\"><strong>{n} relic{s} still riding in the pack.</strong> \
                 {names} {is} carried, not banked — this run has not made a proved exit, and until \
                 it does none of it is theirs.</p>",
                n = pack.len(),
                s = plural(pack.len()),
                names = esc(&sentence_case(&name_list(&pack))),
                is = if pack.len() == 1 { "is" } else { "are" },
            )
        } else {
            String::new()
        };

        // The loss EVERY run takes. Carrying rights attenuate with depth, so the deeper you go the
        // less you can hold: the crown is bought with treasure left lying in the dark.
        let left_note = if left.is_empty() {
            String::new()
        } else {
            format!(
                "<p class=\"rc-left\"><strong>Left in the dark:</strong> {names}. Carrying rights \
                 attenuate with depth — standing on floor {depth} you may hold {ceiling}, so every \
                 step down is paid for in treasure walked past.</p>",
                names = esc(&name_list(&left)),
                depth = self.depth().max(1),
                ceiling = {
                    let ceiling = CARRY_CAP.saturating_sub(self.depth().max(1));
                    format!("{ceiling} relic{}", plural(ceiling as usize))
                },
            )
        };

        let spoils = if banked.is_empty() {
            String::new()
        } else {
            format!(
                "<p class=\"rc-spoils\"><strong>Out with them:</strong> {names}.</p>",
                names = esc(&name_list(&banked)),
            )
        };

        let light_pct = if LIGHT_BREATH == 0 {
            0.0
        } else {
            (self.light_left() as f64 / LIGHT_BREATH as f64) * 100.0
        };
        let light_tone = if self.light_left() <= 4 { " low" } else { "" };
        let depth_pct = if DUNGEON_FLOORS == 0 {
            0.0
        } else {
            (self.depth() as f64 / DUNGEON_FLOORS as f64) * 100.0
        };
        let haul_count = if lost.is_empty() {
            banked.len()
        } else {
            lost.len()
        };
        let haul_pct = if DUNGEON_RELICS == 0 {
            0.0
        } else {
            (haul_count as f64 / DUNGEON_RELICS as f64) * 100.0
        };

        format!(
            "<section class=\"rc rc-{tone}\">\
             <header class=\"rc-head\">\
             <p class=\"rc-eyebrow\">The Descent · {day} · seed {seed}</p>\
             <p class=\"rc-stamp\">{word}</p>\
             <p class=\"rc-who\">{actor}</p>\
             <p class=\"rc-deck\">{headline}</p></header>\
             <div class=\"rc-body\">\
             <div class=\"rc-map\" role=\"img\" aria-label=\"{alt}\" \
             style=\"grid-template-columns:repeat({cols},1fr)\">{grid}</div>\
             <dl class=\"rc-stats\">\
             <div class=\"rc-stat\"><dt>light left</dt>\
             <dd><span class=\"rc-bar{light_tone}\"><i style=\"width:{light_pct:.1}%\"></i></span>\
             <b>{light_left}</b><span class=\"rc-of\">/{breath}</span></dd></div>\
             <div class=\"rc-stat\"><dt>depth reached</dt>\
             <dd><span class=\"rc-bar\"><i style=\"width:{depth_pct:.1}%\"></i></span>\
             <b>{depth}</b><span class=\"rc-of\">/{floors}</span></dd></div>\
             <div class=\"rc-stat\"><dt>{haul_label}</dt>\
             <dd><span class=\"rc-bar{haul_tone}\"><i style=\"width:{haul_pct:.1}%\"></i></span>\
             <b>{haul_count}</b><span class=\"rc-of\">/{relics}</span></dd></div>\
             </dl></div>\
             {spoils}{loss_note}{left_note}\
             <p class=\"rc-legend\">{legend}</p>\
             </section>",
            tone = self.ending.tone(),
            day = esc(day_key),
            seed = esc(seed_tag),
            word = esc(self.ending.word()),
            actor = esc(actor),
            headline = esc(&self.headline()),
            alt = esc(&self.alt_text()),
            cols = MAP_COLS,
            grid = grid,
            light_tone = light_tone,
            light_pct = light_pct,
            light_left = self.light_left(),
            breath = LIGHT_BREATH,
            depth_pct = depth_pct,
            depth = self.depth(),
            floors = DUNGEON_FLOORS,
            haul_label = if lost.is_empty() {
                "relics banked"
            } else {
                "relics LOST"
            },
            haul_tone = if lost.is_empty() { "" } else { " low" },
            haul_pct = haul_pct,
            haul_count = haul_count,
            relics = DUNGEON_RELICS,
            loss_note = loss_note,
            left_note = left_note,
            spoils = spoils,
            legend = esc(legend_line()),
        )
    }

    /// The board's alternative text — a screen reader gets the story, not sixty-six glyph names.
    pub(crate) fn alt_text(&self) -> String {
        let lost = self.lost();
        let banked = self.banked();
        format!(
            "The shaft at the end of the run. Floor {} of {DUNGEON_FLOORS}. \
             {} banked, {} left in the pack{}.",
            self.depth(),
            if banked.is_empty() {
                "Nothing".to_string()
            } else {
                sentence_case(&name_list(&banked))
            },
            if self.in_pack().is_empty() {
                "nothing".to_string()
            } else {
                name_list(&self.in_pack())
            },
            if lost.is_empty() {
                ""
            } else {
                " when the light died"
            },
        )
    }
}

/// The card's own legend — the live surface's legend, minus the affordance line (nothing on a
/// finished run is actionable) and plus the two states the card exists to distinguish.
fn legend_line() -> &'static str {
    "rows: floors 1–4 · @ the pack (never banked) · $ the vault (theirs). \
     columns: floor · way · guardian · then one per relic (1 crown, 2–4 way-keys, 5–8 treasures). \
     > where the run ended · / open way · # shut way · G guardian · x slain · \
     C crown · k way-key · * treasure"
}

/// The custody code of `relic`, or `None` when the replayed state's custody vector is short (a
/// malformed record never reaches here — replay refuses it — but the card must not panic).
fn custody_of(state: &PortableSim, relic: usize) -> Option<u64> {
    state.custody.get(relic).copied()
}

/// Whether the way INTO floor `d` stood open. Way 1 is the mouth; ways 2..=FLOORS are the
/// exercised key-relics, in the state's own `ways` triple.
fn way_open(state: &PortableSim, d: u64) -> bool {
    d <= 1
        || ((2..=DUNGEON_FLOORS).contains(&d)
            && state.ways.get((d - 2) as usize).copied().unwrap_or(0) == 1)
}

fn plural(n: usize) -> &'static str {
    if n == 1 { "" } else { "s" }
}

/// `the Crown of the Deep, the way-2 key and treasure 1` — an Oxford-free list a sentence can hold.
fn name_list(relics: &[usize]) -> String {
    let names: Vec<String> = relics.iter().map(|&relic| relic_name(relic)).collect();
    match names.len() {
        0 => "nothing".to_string(),
        1 => names[0].clone(),
        _ => {
            let (last, rest) = names.split_last().expect("checked non-empty");
            format!("{} and {last}", rest.join(", "))
        }
    }
}

fn sentence_case(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

/// The card's stylesheet. Kept beside the markup that mounts it (the play surface's `PLAY_STYLE`
/// idiom) so the two cannot drift apart, and deliberately HIGH-CONTRAST and compact: this card is
/// screenshotted, thumbnailed and pasted into chats far more often than it is read at full size.
pub(crate) const CARD_STYLE: &str = r#"<style>
.rc{--rc-edge:#334c73;margin:var(--s5) 0;padding:clamp(1rem,3.4vw,1.6rem);border:1px solid var(--rc-edge);border-radius:var(--r-lg);background:linear-gradient(168deg,#0a1120,#05080f 62%);box-shadow:0 26px 60px -34px #000,inset 0 1px 0 rgba(255,255,255,.035)}
.rc-good{--rc-edge:rgba(79,220,160,.5)}.rc-bad{--rc-edge:rgba(255,123,134,.5)}.rc-warn{--rc-edge:rgba(245,200,92,.45)}
.rc-head{margin:0 0 1rem}
.rc-eyebrow{margin:0 0 .5rem;font-family:var(--mono);font-size:var(--t-micro);letter-spacing:.15em;text-transform:uppercase;color:var(--fg-3)}
.rc-stamp{margin:0;font-size:clamp(1.9rem,7.4vw,3.1rem);line-height:.98;font-weight:800;letter-spacing:-.03em;color:var(--good);text-shadow:0 0 34px rgba(79,220,160,.34)}
.rc-bad .rc-stamp{color:var(--bad);text-shadow:0 0 34px rgba(255,123,134,.32)}
.rc-warn .rc-stamp{color:var(--warn);text-shadow:0 0 30px rgba(245,200,92,.26)}
.rc-who{margin:.3rem 0 0;font-family:var(--mono);font-size:var(--t-sm);color:var(--fg-2);overflow-wrap:anywhere}
.rc-deck{margin:.7rem 0 0;font-size:var(--t-lead);line-height:1.5;color:var(--fg);max-width:52ch}
.rc-body{display:grid;grid-template-columns:minmax(0,1.35fr) minmax(0,1fr);gap:clamp(.9rem,3vw,1.6rem);align-items:start}
/* THE SHAFT — a relic keeps its COLUMN, so the eye follows it down the card. */
.rc-map{display:grid;gap:.2rem;padding:.5rem;border:1px solid var(--line-soft);border-radius:var(--r-sm);background:#03060d}
.rc-cell{display:grid;place-items:center;aspect-ratio:1/1;min-width:0;border:1px solid transparent;border-radius:3px;background:rgba(255,255,255,.022);color:#5c6478;font-family:var(--mono);font-size:clamp(.7rem,2.1vw,1.05rem);font-weight:700;line-height:1}
.rc-cell.tag-muted{color:#39415a}
.rc-cell.tag-accent{color:#eaf3ff;background:rgba(92,201,255,.14);border-color:rgba(92,201,255,.44)}
.rc-cell.tag-good{color:var(--good)}.rc-cell.tag-warn{color:var(--warn)}.rc-cell.tag-bad{color:var(--bad)}
.rc-cell.unreached{opacity:.42}
.rc-cell.here{box-shadow:0 0 0 1px rgba(92,201,255,.34)}
/* BANKED — solid, filled, finished. It is theirs and it looks it. */
.rc-cell.banked{color:#02251a;background:linear-gradient(180deg,#63e9b1,#2fb87e);border-color:#7cf0c0;box-shadow:0 0 16px -5px rgba(79,220,160,.95)}
/* LOST — struck through in red. The pack row of a run whose light died. */
.rc-cell.lost{color:#ffb3b9;border-color:rgba(255,123,134,.5);background:linear-gradient(135deg,transparent 43%,rgba(255,123,134,.72) 43%,rgba(255,123,134,.72) 57%,transparent 57%),rgba(255,123,134,.09)}
/* AT RISK — carried by a run that has not ended. Outlined, not filled: not theirs yet. */
.rc-cell.at-risk{color:var(--warn);border-color:rgba(245,200,92,.55);border-style:dashed;background:rgba(245,200,92,.07)}
.rc-stats{margin:0;display:grid;gap:.75rem;align-content:start}
.rc-stat dt{font-family:var(--mono);font-size:var(--t-micro);letter-spacing:.13em;text-transform:uppercase;color:var(--fg-3)}
.rc-stat dd{margin:.3rem 0 0;display:flex;align-items:baseline;gap:.5rem;font-family:var(--mono)}
.rc-stat dd b{font-size:1.35rem;font-weight:800;color:var(--fg);font-variant-numeric:tabular-nums}
.rc-of{color:var(--fg-3);font-size:var(--t-sm)}
.rc-bar{flex:1 1 auto;min-width:2.5rem;height:.5rem;border-radius:999px;background:rgba(255,255,255,.07);box-shadow:inset 0 0 0 1px rgba(255,255,255,.06);overflow:hidden}
.rc-bar i{display:block;height:100%;background:linear-gradient(90deg,#2fb87e,#63e9b1)}
.rc-bar.low i{background:linear-gradient(90deg,#8c3b36,#ff7b86)}
.rc-loss,.rc-risk{margin:1rem 0 0;padding:.75rem .9rem;border-left:3px solid var(--bad);border-radius:0 var(--r-sm) var(--r-sm) 0;background:rgba(255,123,134,.08);color:#ffd6d9;line-height:1.55}
.rc-risk{border-left-color:var(--warn);background:rgba(245,200,92,.07);color:#f6e3b6}
.rc-loss strong{color:#fff}.rc-risk strong{color:#fff}
.rc-spoils{margin:.7rem 0 0;color:var(--fg-2);line-height:1.55}
.rc-spoils strong{color:var(--good)}
.rc-left{margin:.7rem 0 0;color:var(--fg-3);line-height:1.55;font-size:var(--t-sm)}
.rc-left strong{color:var(--fg-2)}
.rc-legend{margin:.9rem 0 0;font-family:var(--mono);font-size:var(--t-micro);line-height:1.75;color:var(--fg-3);overflow-wrap:anywhere}
.rc-text{margin:var(--s4) 0 0}
.rc-text summary{cursor:pointer;font-size:var(--t-sm);color:var(--fg-2);padding:.4rem 0}
.rc-text pre{margin:.5rem 0 0;padding:.85rem;overflow-x:auto;border:1px solid var(--line-soft);border-radius:var(--r-sm);background:#03060d;color:var(--fg-2);font-family:var(--mono);font-size:var(--t-micro);line-height:1.5}
@media(max-width:640px){.rc-body{grid-template-columns:1fr}.rc-map{max-width:100%}.rc-stat dd b{font-size:1.15rem}}
</style>"#;

#[cfg(test)]
mod tests {
    use super::*;

    /// The day-0 shipped map, so a fixture's guardian column means what day 0's means.
    fn world() -> DayWorld {
        dungeon_on_dregg::descent::CANON_WORLD
    }

    fn sim(
        depth: u64,
        spent: u64,
        wounds: u64,
        fate: u64,
        ways: [u64; 3],
        custody: [u64; 8],
    ) -> PortableSim {
        let pack = custody.iter().filter(|&&c| c == CUSTODY_CARRIED).count() as u64;
        let banked = custody.iter().filter(|&&c| c == CUSTODY_BANKED).count() as u64;
        PortableSim {
            depth,
            spent,
            wounds,
            fate,
            ways,
            custody: custody.to_vec(),
            pack,
            banked,
        }
    }

    /// **The run whose light died on floor 3** — the way-4 key in hand, the crown one floor below
    /// and forever out of reach. `flee` was never paid, so nothing is banked and the pack is the
    /// loss. (Day 0's homes are `[4,1,2,3,1,1,2,3]`, so relic 0 lies on floor 4.)
    fn light_died() -> RunStory {
        RunStory::new(
            sim(3, LIGHT_BREATH, 2, 0, [1, 1, 0], [4, 8, 8, 8, 1, 1, 8, 3]),
            world(),
            false,
        )
    }

    /// **The same line, but paid for** — one more light bought the exit, and `flee` moved the whole
    /// pack (crown included) into the vault.
    fn crowned() -> RunStory {
        RunStory::new(
            sim(4, 22, 2, 1, [1, 1, 1], [9, 9, 9, 9, 1, 1, 9, 3]),
            world(),
            true,
        )
    }

    /// **The loss is a DIFFERENT PICTURE from the win.** A relic frozen in the pack when the light
    /// died paints `lost`; a relic a proved exit banked paints `banked`. NON-VACUOUS: the same
    /// relics, the same columns, two endings, two classes — and the dead run's vault is empty
    /// exactly where the settled run's pack is.
    #[test]
    fn a_lost_relic_and_a_banked_relic_do_not_look_the_same() {
        let died = light_died();
        let out = crowned();

        assert_eq!(died.ending(), Ending::LightDied);
        assert_eq!(
            died.lost(),
            vec![1, 2, 3, 6],
            "three keys and a treasure were on them when the light went out"
        );
        assert!(
            died.banked().is_empty(),
            "a run that never fled banked nothing"
        );

        assert_eq!(out.ending(), Ending::Crowned);
        assert!(out.lost().is_empty(), "a settled run loses nothing");
        assert!(out.in_pack().is_empty(), "`flee` empties the pack");
        assert_eq!(out.banked(), vec![0, 1, 2, 3, 6]);

        let died_html = died.html("web:alice", "d1-off", "aabbccdd");
        let out_html = out.html("web:alice", "d1-off", "aabbccdd");
        assert!(
            died_html.contains("rc-cell tag-bad lost"),
            "the lost relics are struck through: {died_html}"
        );
        assert!(
            !died_html.contains(" banked\">"),
            "a dead run has no banked cell: {died_html}"
        );
        assert!(
            out_html.contains("rc-cell tag-good banked"),
            "the banked relics are filled solid: {out_html}"
        );
        assert!(
            !out_html.contains(" lost\">"),
            "a settled run has no lost cell: {out_html}"
        );
        // The loss is said in WORDS as well as in colour — a thumbnail, a screen reader and a
        // text channel all have to carry it.
        assert!(
            died_html.contains("died in the dark") && died_html.contains("the way-4 key"),
            "the loss names what was lost: {died_html}"
        );
        assert!(!out_html.contains("died in the dark"));
        assert!(
            out_html.contains("the Crown of the Deep"),
            "the win names the prize: {out_html}"
        );
        // And the STAT the card leads with flips from a haul to a body count.
        assert!(died_html.contains("relics LOST") && !died_html.contains("relics banked"));
        assert!(out_html.contains("relics banked") && !out_html.contains("relics LOST"));
    }

    /// **The board is the LIVE board.** Rows floors 1..4 then `@` then `$`, `3 + RELICS` wide, one
    /// column per relic — and a relic keeps that column as it travels, which is the whole reason
    /// the picture is worth painting.
    #[test]
    fn the_board_is_the_live_shaft_and_a_relic_keeps_its_column() {
        let story = light_died();
        let cells = story.board();
        assert_eq!(
            cells.len(),
            MAP_COLS * (DUNGEON_FLOORS as usize + 2),
            "four floor rows, the pack row, the vault row"
        );
        assert_eq!(MAP_COLS, 3 + DUNGEON_RELICS);

        let at = |row: usize, col: usize| cells[row * MAP_COLS + col].glyph.as_str();
        assert_eq!(at(2, 0), GLYPH_YOU, "the run ended standing on floor 3");
        assert_eq!(at(4, 0), GLYPH_PACK);
        assert_eq!(at(5, 0), GLYPH_VAULT);
        assert_eq!(at(0, 1), GLYPH_WAY_OPEN, "floor 1 is the mouth");
        assert_eq!(at(3, 1), GLYPH_WAY_SHUT, "way 4 was never unlocked");
        // The crown lies on floor 4 — a row this run never stood on.
        assert_eq!(at(3, 3), GLYPH_CROWN);
        assert_eq!(
            cells[3 * MAP_COLS + 3].flavour,
            Flavour::Unreached,
            "a relic on a floor the run never reached reads as out of reach"
        );
        // Relic 1's COLUMN is 3+1 in every row: it left floor 1 and is in the pack, not the vault.
        assert_eq!(
            at(0, 3 + 1),
            GLYPH_EMPTY,
            "relic 1 no longer lies on floor 1"
        );
        assert_eq!(at(4, 3 + 1), GLYPH_KEY, "relic 1 is in the pack");
        assert_eq!(at(5, 3 + 1), GLYPH_EMPTY, "relic 1 never reached the vault");
        // The vault row is EMPTY across every relic column — that emptiness IS the story.
        for relic in 0..DUNGEON_RELICS {
            assert_eq!(at(5, 3 + relic), GLYPH_EMPTY);
        }
    }

    /// **Nothing on a finished run is highlighted.** The text projection brackets a highlighted
    /// cell and the live legend reads that bracket as "you may act on it NOW" — a run-card that
    /// borrowed the bracket for a second meaning would make one glyph mean two things across two
    /// surfaces.
    #[test]
    fn the_run_card_never_borrows_the_actionable_bracket() {
        let text = light_died().text_card("web:alice", "d1-off");
        assert!(
            !text.contains('['),
            "the actionable bracket does not appear on a finished run: {text}"
        );
        // The caption is what carries the meaning instead — and it says LOST, out loud.
        assert!(text.contains("LOST — the light died"), "{text}");
        assert!(text.contains("never reached"), "{text}");
    }

    /// **The unfinished prefix is not dressed as a story.** A run with light left has not ended,
    /// and the card says so instead of reporting a triumphant zero.
    #[test]
    fn an_unfinished_prefix_reads_as_unfinished() {
        let story = RunStory::new(
            sim(1, 2, 0, 0, [0, 0, 0], [4, 1, 2, 3, 1, 1, 2, 3]),
            world(),
            false,
        );
        assert_eq!(story.ending(), Ending::Delving);
        assert!(
            story.lost().is_empty(),
            "a run with light left has lost nothing YET"
        );
        assert!(
            story.headline().contains("has not ended"),
            "{}",
            story.headline()
        );
    }

    /// **An unfinished run's pack is AT RISK, not banked and not lost.** This is the loss beat for
    /// the common case: a player who walked away carrying four relics banked nothing, and the card
    /// must not paint that pack as a haul. NON-VACUOUS: the same custody after a `flee` paints
    /// `banked` instead.
    #[test]
    fn an_unfinished_runs_pack_paints_as_unbanked_risk() {
        let walked_away = RunStory::new(
            sim(3, 18, 2, 0, [1, 1, 0], [4, 8, 8, 8, 1, 1, 8, 3]),
            world(),
            false,
        );
        assert_eq!(walked_away.ending(), Ending::Delving);
        assert_eq!(walked_away.in_pack(), vec![1, 2, 3, 6]);
        assert!(
            walked_away.banked().is_empty() && walked_away.lost().is_empty(),
            "not banked, and not lost either — it is UNRESOLVED"
        );
        let html = walked_away.html("web:alice", "d1-off", "aabbccdd");
        assert!(
            html.contains("rc-cell tag-warn at-risk"),
            "the carried relics are outlined, not filled: {html}"
        );
        assert!(
            html.contains("still riding in the pack") && html.contains("none of it is theirs"),
            "the risk is said in words: {html}"
        );
        assert!(
            !html.contains("rc-cell tag-good banked"),
            "an unfinished run has banked nothing: {html}"
        );
    }

    /// **Every run pays the carry cap, and the card names the price.** Carrying rights attenuate
    /// with depth (`pack + depth <= CAP`), so a run standing on floor 4 holds at most `CAP - 4`:
    /// the crown is bought with treasure walked past. A card that only reported the haul would
    /// hide the game's central trade.
    #[test]
    fn the_card_names_what_the_run_walked_past() {
        let out = crowned();
        // Relics 4, 5 and 7 never left the shaft.
        assert_eq!(out.left_in_the_dark(), vec![4, 5, 7]);
        let html = out.html("web:alice", "d1-off", "aabbccdd");
        assert!(
            html.contains("Left in the dark") && html.contains("Carrying rights"),
            "the card names the treasure walked past: {html}"
        );
        assert!(
            html.contains(&format!("you may hold {} relic", CARRY_CAP - 4)),
            "the ceiling quoted is the ceiling AT THAT DEPTH, not the flat cap: {html}"
        );
        assert!(
            out.headline().contains("3 relics left in the dark"),
            "{}",
            out.headline()
        );
        // The text form carries it too — a pasted card must not be a rosier card.
        assert!(
            out.text_card("web:alice", "d1-off")
                .contains("left in the dark:")
        );
    }

    /// **The light clock is the game's clock.** Spent + left is always the Lean-sourced BREATH, and
    /// a burnt-out run reads zero rather than going negative.
    #[test]
    fn the_light_clock_reads_against_the_games_own_breath() {
        let burnt = RunStory::new(
            sim(2, LIGHT_BREATH, 1, 0, [1, 0, 0], [4, 8, 2, 3, 1, 1, 2, 3]),
            world(),
            false,
        );
        assert_eq!(burnt.light_left(), 0);
        assert_eq!(burnt.light_spent(), LIGHT_BREATH);
        let fresh = RunStory::new(
            sim(1, 1, 0, 0, [0, 0, 0], [4, 1, 2, 3, 1, 1, 2, 3]),
            world(),
            false,
        );
        assert_eq!(fresh.light_left() + fresh.light_spent(), LIGHT_BREATH);
    }

    /// **The day's own map decides the guardian.** A day whose floor-3 guardian has 3 vitality does
    /// not read as slain at 2 wounds just because day 0's would. (This is the bug a hard-coded
    /// `guard_hp` table ships silently on every beacon day.)
    #[test]
    fn the_guardian_column_reads_the_days_drawn_vitality() {
        let state = sim(3, 20, 2, 0, [1, 1, 0], [4, 8, 8, 3, 1, 1, 2, 3]);
        let canon = RunStory::new(state.clone(), world(), false);
        let tough = RunStory::new(
            state,
            DayWorld {
                homes: dungeon_on_dregg::descent::HOME,
                ghp: [0, 1, 1, 3, 2],
            },
            false,
        );
        let guardian = |story: &RunStory| story.board()[2 * MAP_COLS + 2].glyph.clone();
        assert_eq!(
            guardian(&canon),
            GLYPH_GUARDIAN_SLAIN,
            "2 wounds kills a 2-hp guardian"
        );
        assert_eq!(
            guardian(&tough),
            GLYPH_GUARDIAN,
            "2 wounds does NOT kill a 3-hp one"
        );
    }

    /// **The copyable card, pinned verbatim.** This is the artifact that gets pasted into a chat,
    /// so its exact shape is a product surface, not an implementation detail: the board columns
    /// must line up under a monospace font, every row must carry the caption that makes it mean
    /// something, and the loss must be readable with no colour and no CSS at all.
    #[test]
    fn the_text_card_is_readable_with_no_colour_at_all() {
        let rendered = light_died().text_card("web:alice", "d20260-off");
        let expected = concat!(
            "THE LIGHT IS DEAD — web:alice · d20260-off\n",
            "The light burned out on floor 3 carrying the way-2 key, the way-3 key, the way-4 key ",
            "and treasure 3 — never banked, never theirs. 4 relics left in the dark.\n",
            "\n",
            " 1  /  G  ·  ·  ·  ·  *  *  ·  ·    floor 1\n",
            " 2  /  G  ·  ·  ·  ·  ·  ·  ·  ·    floor 2\n",
            " >  /  x  ·  ·  ·  ·  ·  ·  ·  *    floor 3 — the run ended here\n",
            " 4  #  G  C  ·  ·  ·  ·  ·  ·  ·    floor 4 — never reached\n",
            " @  ·  ·  ·  k  k  k  ·  ·  *  ·    LOST — the light died with 4 relics still on them\n",
            " $  ·  ·  ·  ·  ·  ·  ·  ·  ·  ·    banked — nothing; no proved exit was ever made\n",
            "\n",
            "light  ░░░░░░░░░░░░  0 left of 26 (26 spent)\n",
            "depth  3 of 4\n",
            "\n",
            "left in the dark: the Crown of the Deep, treasure 1, treasure 2 and treasure 4\n",
            "\n",
            "rows: floors 1–4 · @ the pack (never banked) · $ the vault (theirs). columns: floor · ",
            "way · guardian · then one per relic (1 crown, 2–4 way-keys, 5–8 treasures). ",
            "> where the run ended · / open way · # shut way · G guardian · x slain · C crown · ",
            "k way-key · * treasure\n",
        );
        assert_eq!(
            rendered, expected,
            "\n--- ACTUAL ---\n{rendered}\n--- EXPECTED ---\n{expected}"
        );
    }

    /// The same pin for the card people will actually post: the crowned exit. Two goldens rather
    /// than one because the win and the loss are DIFFERENT cards, and a regression that collapsed
    /// them into one would otherwise pass on whichever half was pinned.
    #[test]
    fn the_crowned_text_card_reads_as_a_haul_and_still_names_the_cost() {
        let rendered = crowned().text_card("web:alice", "d20260-off");
        let expected = concat!(
            "CROWNED — web:alice · d20260-off\n",
            "The Crown of the Deep came out of floor 4 — 5 relics banked, 4 light left of 26. ",
            "3 relics left in the dark.\n",
            "\n",
            " 1  /  G  ·  ·  ·  ·  *  *  ·  ·    floor 1\n",
            " 2  /  G  ·  ·  ·  ·  ·  ·  ·  ·    floor 2\n",
            " 3  /  G  ·  ·  ·  ·  ·  ·  ·  *    floor 3\n",
            " >  /  x  ·  ·  ·  ·  ·  ·  ·  ·    floor 4 — the run ended here\n",
            " @  ·  ·  ·  ·  ·  ·  ·  ·  ·  ·    pack — emptied into the vault by the exit\n",
            " $  ·  ·  C  k  k  k  ·  ·  *  ·    banked — 5 relics came out\n",
            "\n",
            "light  ██░░░░░░░░░░  4 left of 26 (22 spent)\n",
            "depth  4 of 4\n",
            "\n",
            "left in the dark: treasure 1, treasure 2 and treasure 4\n",
            "\n",
            "rows: floors 1–4 · @ the pack (never banked) · $ the vault (theirs). columns: floor · ",
            "way · guardian · then one per relic (1 crown, 2–4 way-keys, 5–8 treasures). ",
            "> where the run ended · / open way · # shut way · G guardian · x slain · C crown · ",
            "k way-key · * treasure\n",
        );
        assert_eq!(
            rendered, expected,
            "\n--- ACTUAL ---\n{rendered}\n--- EXPECTED ---\n{expected}"
        );
    }

    /// **A short custody vector cannot panic the card.** Replay refuses a malformed record long
    /// before rendering, but a renderer that indexes blind is one bad row away from a 500.
    #[test]
    fn a_truncated_custody_vector_renders_instead_of_panicking() {
        let mut state = sim(2, 8, 1, 0, [1, 0, 0], [4, 8, 2, 3, 1, 1, 2, 3]);
        state.custody.truncate(3);
        let story = RunStory::new(state, world(), false);
        assert_eq!(
            story.board().len(),
            MAP_COLS * (DUNGEON_FLOORS as usize + 2)
        );
        let _ = story.html("web:alice", "d1-off", "aabbccdd");
        let _ = story.text_card("web:alice", "d1-off");
    }
}
