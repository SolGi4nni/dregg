//! # **THE CATALOG-WIDE FLOW HARNESS** — every offering is USER-TESTED by being driven.
//!
//! On 2026-07-25 four real UX defects were found by hand-surveying surfaces one at a time:
//!
//! 1. **tug leaked a seat's hand through BUTTON LABELS** while its fog *sections* were correct
//!    (`7f216ec8b`). The spectator test only looked for `"Your hand"` / `"(hidden)"`, so it could
//!    never see a leak that lived in an action row's label.
//! 2. **a sealed-bid auction never showed a bidder their own bid** (`7f216ec8b`).
//! 3. **the dungeon re-rendered BYTE-IDENTICALLY after a 20-HP loss** (`0f8e46d09`) — "what just
//!    happened" was structurally unrecoverable from the page.
//! 4. **`ViewNode::Pill` had NO plain-text projection** (`deos_view::text` dropped it *by design*),
//!    so a chat surface learned nothing about phase. Hit independently by two lanes.
//!
//! Every one of those is a GENERAL property. Surveying by hand finds them one at a time, one
//! offering at a time, and only for the offerings someone happened to open. This file checks them
//! ACROSS THE WHOLE CATALOG, on the deployed router, by DRIVING each offering:
//! open → read the page → take an act the page itself offered → read the page again.
//!
//! ## What it enumerates
//!
//! The **live registry of the deployed app** — `make_app_parts()`'s own `CatalogState`
//! (`list_offerings()`), not a list written here. [`the_harness_enumerates_the_whole_live_catalog`]
//! pins that live set against [`dreggnet_catalog::CATALOG_KEYS`] in BOTH directions, so a new
//! offering is covered the day it lands and cannot be quietly dropped from the sweep either.
//!
//! ## What it asserts (and why each invariant exists)
//!
//! | code | invariant | born from |
//! |---|---|---|
//! | `directive` | the page says what to do NOW, not only what the state IS | automatafl's plaque convention; the whole "it looks like a debug view" complaint |
//! | `no-debug` | no `{:?}`-shaped dump reaches user-facing text | a Debug dump is where secrets hide, and reads as a debug view |
//! | `prose-parity` | every `Pill`'s words also reach `render_text` | defect 4 — a chat user learns nothing about phase |
//! | `act-lands` | the first ENABLED act the page offers is accepted by the executor | a page offering a move the executor refuses is a dead affordance |
//! | `state-visible` | the page's visible text CHANGES when a turn lands | defect 3, generalised |
//! | `fog` | (hidden-information offerings) a spectator reads no seat-private token — **controls included** | defect 1 |
//!
//! ⚑ **NEVER a hardcoded `(method, index)`.** `arg` indexes the offering's LIVE decision list;
//! `demo_playthrough` hardcoded `("comp", 3)` and went stale the moment tug grew a real decision
//! space. Every act this harness fires is read off the page that offered it
//! ([`common::offered_acts`]).
//!
//! ## Failures are a TABLE, not a red
//!
//! A bare "assertion failed" across 23 offerings is useless. Every check records a per-offering,
//! per-invariant cell with the offending text, the whole grid prints on every run, and the panic
//! carries the full table — one run gives the whole catalog's UX state.
//!
//! ## What it sweeps — EVERYTHING REGISTERED, with the ship list as a stricter TIER
//!
//! ⚑ The catalog now has two sizes: `list_offerings()` is all 23, and
//! [`dreggnet_catalog::SHIPPED_KEYS`] (`descent` · `automatafl` · `tug`) is the curated shelf a
//! stranger is actually shown. **This harness sweeps the WHOLE registry, deliberately** — the
//! alternative makes "unadvertised" quietly mean "unmaintained", and an offering that rots
//! off-shelf is exactly the thing nobody notices until it is re-listed.
//!
//! The ship list is layered on as a **stricter tier**, never a smaller sweep: every non-PASS cell
//! on an advertised offering is reported again in its own block, because an allowance on the shelf
//! ember points people at is worth strictly more than the same allowance on an experiment. The
//! list is READ, never re-typed here, so re-listing an offering silently promotes its row.
//!
//! ## Invariants this does NOT yet assert — named, not forgotten
//!
//! Both come out of the first-time-reader QA sweep (`docs/reference/UX-QA-SWEEP-2026-07-26.md`),
//! which is this file's complement: a test can assert "the bytes differ after an act"; only a
//! reader can say "they differ and I still cannot tell what I did."
//!
//! * **`arg` is a user-editable number box on every affordance** (QA §1), beside a button whose
//!   label already names the target — so the label is NOT BINDING: change the box, press the
//!   button, act on something else. It bites hardest where two rows differ only by index (trade
//!   ships two `Ember Cloak`s). Not asserted here because the FIX and the assertion need the same
//!   missing thing: `deos_view::MenuItem` does not carry `Action::wants_text`, so the renderer
//!   cannot tell "this affordance solicits a value" from "this affordance's arg is its identity".
//!   That is the SAME cross-crate change already parked under the `hermes`/`names`/`doc`
//!   allowances below — one fix closes both.
//! * **"No surface states the same fact twice in one projection."** Mechanically checkable and it
//!   would have caught a collision two lanes created inside a day: `0f8e46d09` gave every pill it
//!   added a hand-written prose mirror *because* `deos_view::text` dropped pills, and the shared
//!   fix here now paints those pills too — so descent-campaign and dungeon each say their phase
//!   twice in chat (redundant, checked: NOT contradictory). Not asserted yet because "the same
//!   fact" needs a definition sharper than token containment, which would fire on legitimate
//!   summary-then-detail. TODO with the copy pass that trims the mirrors.
//!
//! ## Exemptions are NAMED, and a stale one is a FAILURE
//!
//! Where an offering needs real design work rather than a bodge, [`EXEMPTIONS`] records it with a
//! reason and a TODO. An exempt cell is not silently skipped: it is CHECKED anyway, and an
//! exemption whose invariant now PASSES fails the run as a stale allowance. There is no
//! `#[ignore]` and no silently-skipped offering here — that is precisely the failure mode this
//! repo keeps re-finding.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use axum::Router;
use axum::http::StatusCode;
use deos_view::ViewNode;
use deos_view::text::render_text;
use dreggnet_offerings::{Action, DreggIdentity, OfferingHost, Outcome, SessionId};

mod common;

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE INVARIANTS
// ─────────────────────────────────────────────────────────────────────────────────────────

/// The page says what to do NOW. The repo's convention (set by automatafl, adopted by tug, and
/// PROMOTED TYPOGRAPHICALLY by the shared skin — `.af-table .deos-section.tag-accent>.prose:first-of-type`
/// renders as a serif lead on a violet rule) is: **a plaque tagged `accent`, whose FIRST paragraph
/// is the one sentence saying what to do right now.** So the check is structural, not a guess at
/// imperative mood: the surface must emit that plaque and that paragraph.
const INV_DIRECTIVE: &str = "directive";
/// No `{:?}`-shaped Debug dump reaches user-facing text. Checked on the RENDERED text, never on the
/// source: `format!("seat {s:?}")` over a fieldless enum prints `seat A`, which is fine prose, while
/// a struct or tuple Debug prints `Foo { bar: 3 }` / `Some("…")`, which is a debug view and is where
/// a secret hides.
const INV_NO_DEBUG: &str = "no-debug";
/// Anything a `Pill` says must also reach `render_text` — the prose projection every chat transport
/// (Telegram, WeChat) renders. `deos_view::text` used to drop `Pill` by design, so a phase/status
/// carried ONLY by a pill was invisible to every chat user. This was a REAL gap and it was WIDE:
/// **15 of the 23 offerings failed this on the harness's first run**, and it is fixed at the source
/// (a literal pill now paints as `[badge]`). This cell keeps the fix honest for the next offering.
const INV_PROSE_PARITY: &str = "prose-parity";
/// The first ENABLED act the page offers is accepted by the executor — read `(turn, arg)` off the
/// page and POST it. A page that offers a move the executor refuses is a dead affordance.
const INV_ACT_LANDS: &str = "act-lands";
/// The page's VISIBLE TEXT changes when a turn lands. The dungeon bug, generalised: a surface that
/// re-renders identically after a real state change has made "what just happened" structurally
/// unrecoverable. Compared on visible text (tags stripped) so the per-request form token — which
/// changes with the head and would make this pass for free — cannot launder it.
const INV_STATE_VISIBLE: &str = "state-visible";
/// For an offering declaring `hidden_information() == true`: a viewer holding NO seat reads no
/// seat-private token — and the check runs over the page's whole visible text, CONTROLS INCLUDED,
/// because that is exactly where tug's leak lived.
const INV_FOG: &str = "fog";

/// Every invariant, in table order.
const INVARIANTS: [&str; 6] = [
    INV_DIRECTIVE,
    INV_NO_DEBUG,
    INV_PROSE_PARITY,
    INV_ACT_LANDS,
    INV_STATE_VISIBLE,
    INV_FOG,
];

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE NAMED ALLOWANCES
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **A documented, named per-offering exemption** — debt made VISIBLE and ENUMERABLE, never a
/// silent skip. The cell is still evaluated; the verdict is merely downgraded from `FAIL` to
/// `EXEMPT`, and an exemption whose invariant now passes is itself a FAILURE (a stale allowance
/// hides the fact that the work is done and the gate could be tightened).
struct Exemption {
    key: &'static str,
    invariant: &'static str,
    /// Why this cannot be fixed cheaply — the design work it actually needs.
    reason: &'static str,
}

/// The live allowance list. Keep it SHORT and keep every entry's reason true.
const EXEMPTIONS: &[Exemption] = &[
    // ── THE TEXT-AFFORDANCE CARRIER GAP. One cause, three offerings. ───────────────────────────
    Exemption {
        key: "hermes",
        invariant: INV_ACT_LANDS,
        reason: "A TEXT-TAKING AFFORDANCE HAS NO CARRIER ON THE WEB. `hermes`'s `prompt` is an \
                 `Action` with `wants_text`, and the executor correctly refuses it with \
                 \"no prompt supplied … the button label is not a prompt\". Nothing about the \
                 offering is wrong; the WEB PATH drops the payload at three points — \
                 `deos_view::MenuItem` carries no `wants_text` flag, `render_catalog_forms` \
                 renders no text input, and `dreggnet_web::OfferingActForm` has no `text` field. \
                 TODO: thread it. `MenuItem` is a shared struct with many literal constructions \
                 across deos-view/dreggnet-*/discord-bot, so widening it is a cross-crate change \
                 that must land as one piece — NOT a per-offering patch, and never a bodge that \
                 rides the payload on the label (dreggnet-doc already did that once).",
    },
    Exemption {
        key: "names",
        invariant: INV_ACT_LANDS,
        reason: "The same missing carrier as `hermes`: `register` is `wants_text` and is refused \
                 \"no name supplied — the `register` affordance needs a name typed into its text \
                 payload\". Same TODO, same one cross-crate fix.",
    },
    Exemption {
        key: "doc",
        invariant: INV_ACT_LANDS,
        reason: "TWO causes, both real. (1) The same missing text carrier — `insert` / \
                 `set the title` are `wants_text`. (2) A FRESH DOCUMENT HAS NO EDITOR: \
                 `DocOffering::actions_for` enables an edit only for an identity holding the \
                 region's edit cap, and a newly-opened document has an empty roster, so the first \
                 visitor is offered three dimmed controls and no way to become a collaborator. \
                 TODO: that second half is a CAP-MODEL decision (claim-on-first-write, the way \
                 `SeatedTug` claims a seat, versus an explicit invite seam) on a verified \
                 offering — design work, not a patch.",
    },
    // ── ON THE SHELF, AND OWNED BY ANOTHER LANE RIGHT NOW. ─────────────────────────────────────
    Exemption {
        key: "automatafl",
        invariant: INV_FOG,
        reason: "⚑ A LIVE DEFECT ON THE SHIPPED SHELF, FOUND BY THIS HARNESS AND CURRENTLY OWNED \
                 BY ANOTHER LANE. Once both seats are taken, a viewer holding NEITHER is still \
                 served an ENABLED `Resolve the round …` control: the board CELLS go inert for a \
                 spectator (`playable = false`) but the phase MENU is not gated on holding a seat, \
                 so `reveal`/`resolve` stay live for anyone. The page meanwhile tells that viewer \
                 \"every control is inert\" — independently confirmed by a first-time reader who \
                 pressed one and changed their seat, their hand and the turn counter \
                 (docs/reference/UX-QA-SWEEP-2026-07-26.md §2). NOT fixed here on purpose: a \
                 sibling lane holds `dregg-automatafl`'s surface this session, and two lanes \
                 editing one seat-gating rule is how the hole gets re-opened. This allowance is \
                 SELF-RETIRING — the run fails as a STALE ALLOWANCE the moment the gate lands, \
                 which is the prompt to delete it.",
    },
    // ── THE READ SURFACES. Real, and honestly named rather than laundered. ─────────────────────
    Exemption {
        key: "cheevos",
        invariant: INV_ACT_LANDS,
        reason: "A READ-ONLY SHELF BY CONSTRUCTION: `CheevoOffering::actions` returns an empty \
                 vec and `advance` refuses everything — an achievement is earned by playing, not \
                 claimed on this page, and the surface now SAYS so in its directive. The residual \
                 is still real: a player who opens it has nowhere to go next. TODO: `ViewNode` has \
                 no LINK-OUT variant, so the shelf cannot offer \"go play the Descent\" as \
                 anything but a dead POST button. Adding one is an IR change shared with `tavern`.",
    },
    Exemption {
        key: "tavern",
        invariant: INV_ACT_LANDS,
        reason: "A READ MIRROR: posting / seating / partying up are real attributed turns on the \
                 LIVE tavern node, not moves on this surface, so `actions` is empty and `advance` \
                 refuses. This run's fix removed the WORSE half — the page used to paint an \
                 enabled `Enter …` submit that could only ever answer \"that affordance is not on \
                 the current surface\" — and it is now a dimmed row beside prose naming the real \
                 hall. TODO: the same missing LINK-OUT node in `ViewNode` as `cheevos`; until it \
                 exists a destination cannot be offered as anything but a turn.",
    },
];

fn exemption_for(key: &str, invariant: &str) -> Option<&'static Exemption> {
    EXEMPTIONS
        .iter()
        .find(|e| e.key == key && e.invariant == invariant)
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE RESULT GRID
// ─────────────────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Pass,
    Fail,
    /// Documented allowance (see [`EXEMPTIONS`]) — the check ran and did not hold.
    Exempt,
    /// The invariant does not apply to this offering (e.g. `fog` on a full-information offering).
    NotApplicable,
}

impl Verdict {
    fn mark(self) -> &'static str {
        match self {
            Verdict::Pass => "PASS",
            Verdict::Fail => "FAIL",
            Verdict::Exempt => "exempt",
            Verdict::NotApplicable => "n/a",
        }
    }
}

struct Cell {
    verdict: Verdict,
    detail: String,
}

/// One offering's row.
struct Row {
    key: String,
    cells: BTreeMap<&'static str, Cell>,
}

impl Row {
    fn new(key: &str) -> Self {
        Row {
            key: key.to_string(),
            cells: BTreeMap::new(),
        }
    }

    /// Record a check's outcome, routing a failure through the allowance list.
    fn record(&mut self, invariant: &'static str, held: bool, detail: impl Into<String>) {
        let detail = detail.into();
        let verdict = match (held, exemption_for(&self.key, invariant)) {
            (true, _) => Verdict::Pass,
            (false, Some(_)) => Verdict::Exempt,
            (false, None) => Verdict::Fail,
        };
        self.cells.insert(invariant, Cell { verdict, detail });
    }

    fn not_applicable(&mut self, invariant: &'static str, why: impl Into<String>) {
        self.cells.insert(
            invariant,
            Cell {
                verdict: Verdict::NotApplicable,
                detail: why.into(),
            },
        );
    }

    /// Mark every not-yet-recorded invariant as failed for one shared reason (the offering never
    /// rendered at all, so no per-invariant evidence exists).
    fn fail_rest(&mut self, why: &str) {
        for invariant in INVARIANTS {
            self.cells.entry(invariant).or_insert(Cell {
                verdict: match exemption_for(&self.key, invariant) {
                    Some(_) => Verdict::Exempt,
                    None => Verdict::Fail,
                },
                detail: why.to_string(),
            });
        }
    }

    fn verdict(&self, invariant: &str) -> Verdict {
        self.cells
            .get(invariant)
            .map(|c| c.verdict)
            .unwrap_or(Verdict::Fail)
    }
}

/// Render the whole grid — every offering × every invariant — plus the failure detail beneath it.
fn render_table(rows: &[Row]) -> String {
    let key_w = rows.iter().map(|r| r.key.len()).max().unwrap_or(8).max(8);
    let mut out = String::new();
    let _ = write!(out, "\n{:<key_w$}", "offering", key_w = key_w);
    for invariant in INVARIANTS {
        let _ = write!(out, " │ {invariant:^14}");
    }
    out.push('\n');
    out.push_str(&"─".repeat(key_w + INVARIANTS.len() * 17));
    out.push('\n');
    for row in rows {
        let _ = write!(out, "{:<key_w$}", row.key, key_w = key_w);
        for invariant in INVARIANTS {
            let mark = row
                .cells
                .get(invariant)
                .map(|c| c.verdict.mark())
                .unwrap_or("?");
            let _ = write!(out, " │ {mark:^14}");
        }
        out.push('\n');
    }

    let mut notes = String::new();
    for row in rows {
        for invariant in INVARIANTS {
            let Some(cell) = row.cells.get(invariant) else {
                continue;
            };
            match cell.verdict {
                Verdict::Fail => {
                    let _ = write!(notes, "\n  FAIL   {}/{invariant}: {}", row.key, cell.detail);
                }
                Verdict::Exempt => {
                    let reason = exemption_for(&row.key, invariant)
                        .map(|e| e.reason)
                        .unwrap_or("(no reason recorded)");
                    let _ = write!(
                        notes,
                        "\n  exempt {}/{invariant}: {}\n           reason: {reason}",
                        row.key, cell.detail
                    );
                }
                _ => {}
            }
        }
    }
    if !notes.is_empty() {
        out.push_str("\nDETAIL");
        out.push_str(&notes);
        out.push('\n');
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// READING A RENDERED PAGE THE WAY A PERSON DOES
// ─────────────────────────────────────────────────────────────────────────────────────────

/// The text a person actually READS off a rendered fragment: tags stripped, entities unescaped,
/// whitespace collapsed. Everything a hidden input carries — including the per-request game form
/// token, which changes with the head — is EXCLUDED, which is what keeps `state-visible` honest.
fn visible_text(html: &str) -> String {
    let mut out = String::new();
    let bytes: Vec<char> = html.chars().collect();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == '<' {
            // Skip a whole <script>/<style> element, contents included.
            let rest: String = bytes[i..].iter().take(8).collect::<String>().to_lowercase();
            let skip_to = if rest.starts_with("<script") {
                Some("</script>")
            } else if rest.starts_with("<style") {
                Some("</style>")
            } else {
                None
            };
            if let Some(close) = skip_to {
                let tail: String = bytes[i..].iter().collect();
                match tail.to_lowercase().find(close) {
                    Some(at) => {
                        i += tail[..at + close.len()].chars().count();
                        out.push(' ');
                        continue;
                    }
                    None => break,
                }
            }
            while i < bytes.len() && bytes[i] != '>' {
                i += 1;
            }
            i += 1;
            out.push(' ');
            continue;
        }
        out.push(bytes[i]);
        i += 1;
    }
    let out = out
        .replace("&quot;", "\"")
        .replace("&#39;", "'")
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&amp;", "&");
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The page's text with every CONTROL LABEL removed — the prose half alone.
///
/// The fog check reads a SEAT's secrets from this and hunts for them in the watcher's WHOLE page.
/// The asymmetry is deliberate and is what makes the check usable: a control label's presence
/// depends on whose turn it is, so a label-derived "secret" is really just an affordance the other
/// seat is not being offered this instant (the word "put", out of tug's `Secret — put a favor face
/// down`, was flagged as a leak on the first run). A seat's genuine secrets — its cards, its
/// sealed move — are stated in the PROSE too, so nothing real is lost, while
/// [`control_labels`] keeps the leak side looking exactly where tug's leak lived.
fn visible_text_sans_controls(html: &str) -> String {
    let mut stripped = String::new();
    let mut rest = html;
    while let Some((before, after)) = rest.split_once("<button") {
        stripped.push_str(before);
        stripped.push(' ');
        rest = match after.split_once("</button>") {
            Some((_, tail)) => tail,
            None => "",
        };
    }
    stripped.push_str(rest);
    visible_text(&stripped)
}

/// Just the CONTROL LABELS — every `<button>`'s text. Called out separately from the prose because
/// the tug leak lived HERE and a prose-only fog test could not see it.
fn control_labels(html: &str) -> Vec<String> {
    let mut out = Vec::new();
    for chunk in html.split("<button").skip(1) {
        let Some((_attrs, rest)) = chunk.split_once('>') else {
            continue;
        };
        let Some((inner, _)) = rest.split_once("</button>") else {
            continue;
        };
        let label = visible_text(inner);
        if !label.is_empty() {
            out.push(label);
        }
    }
    out
}

/// **Does this user-facing text carry a `{:?}` dump?** Returns the offending excerpts.
///
/// Deliberately conservative — only shapes a Rust `Debug` impl produces and ordinary prose does
/// not. A fieldless-enum Debug (`format!("seat {s:?}")` → `seat A`) is NOT a dump and is not
/// flagged; a struct/tuple/Option/collection Debug is.
fn debug_dump_hits(text: &str) -> Vec<String> {
    let chars: Vec<char> = text.chars().collect();
    let mut hits = Vec::new();
    let excerpt = |at: usize| -> String {
        let lo = at.saturating_sub(24);
        let hi = (at + 56).min(chars.len());
        chars[lo..hi].iter().collect::<String>()
    };
    let is_ident = |c: char| c.is_alphanumeric() || c == '_';

    for i in 0..chars.len() {
        // ── (1) STRUCT DEBUG: `Ident { field: `
        if chars[i] == '{' {
            // A Rust identifier, then optional space, immediately before the brace.
            let mut j = i;
            while j > 0 && chars[j - 1] == ' ' {
                j -= 1;
            }
            let end = j;
            while j > 0 && is_ident(chars[j - 1]) {
                j -= 1;
            }
            let name: String = chars[j..end].iter().collect();
            let named = name.chars().next().is_some_and(|c| c.is_uppercase());
            // …and a `field: ` right after the brace.
            let mut k = i + 1;
            while k < chars.len() && chars[k] == ' ' {
                k += 1;
            }
            let fstart = k;
            while k < chars.len() && is_ident(chars[k]) {
                k += 1;
            }
            let has_field = k > fstart && k < chars.len() && chars[k] == ':';
            if named && has_field {
                hits.push(excerpt(j));
            }
        }
        // ── (2) TUPLE / VARIANT DEBUG: `Ident("…")`, `Ident(3)`, `Some([`
        if chars[i] == '(' && i > 0 && is_ident(chars[i - 1]) {
            let mut j = i;
            while j > 0 && is_ident(chars[j - 1]) {
                j -= 1;
            }
            let name: String = chars[j..i].iter().collect();
            let camel = name.chars().next().is_some_and(|c| c.is_uppercase())
                && name.chars().skip(1).any(|c| c.is_lowercase());
            let payload = chars.get(i + 1).copied();
            let debugish = matches!(payload, Some('"') | Some('[') | Some('{'))
                || (matches!(payload, Some(c) if c.is_ascii_digit())
                    && name.chars().skip(1).all(|c| !c.is_ascii_digit()));
            if camel && debugish {
                hits.push(excerpt(j));
            }
        }
        // ── (3) COLLECTION DEBUG: `[1, 2, 3` / `["a", "b"`
        if chars[i] == '[' {
            let tail: String = chars[i + 1..(i + 24).min(chars.len())].iter().collect();
            let numeric = tail
                .split(", ")
                .take(3)
                .filter(|t| !t.is_empty() && t.chars().all(|c| c.is_ascii_digit()))
                .count()
                >= 3;
            let quoted = tail.starts_with('"') && tail.contains("\", \"");
            if numeric || quoted {
                hits.push(excerpt(i));
            }
        }
    }
    hits.sort();
    hits.dedup();
    hits.truncate(3);
    hits
}

/// **Is there a DIRECTIVE plaque?** The convention the shared skin promotes typographically —
/// `.af-table .deos-section.tag-accent > .prose:first-of-type` renders as a serif lead on a violet
/// rule — is: **a plaque tagged `accent`, whose first DIRECT-CHILD paragraph is the sentence saying
/// what to do now.** Returns that sentence.
///
/// ⚑ Direct child, tracked by depth, because the CSS says `>`. A first pass matched the first
/// `<p class="prose">` anywhere inside the plaque and handed back a row of a table nested three
/// levels down — a FALSE PASS on a surface with no directive at all (tavern's LFG board). A row of
/// data is not a directive no matter how early it appears.
fn directive_of(html: &str) -> Option<String> {
    const OPENER: &str = "<section class=\"deos-section tag-accent\">";
    'plaque: for start in html.match_indices(OPENER).map(|(i, _)| i) {
        let body = &html[start + OPENER.len()..];
        let mut depth = 0i32;
        let mut i = 0usize;
        while let Some(next) = body[i..].find('<') {
            let at = i + next;
            let tail = &body[at..];
            if tail.starts_with("</section>") {
                if depth == 0 {
                    continue 'plaque; // this plaque closed with no direct prose
                }
                depth -= 1;
                i = at + "</section>".len();
            } else if tail.starts_with("</div>") || tail.starts_with("</form>") {
                depth -= 1;
                i = at + 6;
            } else if tail.starts_with("<section") || tail.starts_with("<div") {
                depth += 1;
                i = at + 4;
            } else if tail.starts_with("<form") {
                depth += 1;
                i = at + 5;
            } else if depth == 0 && tail.starts_with("<p class=\"prose\">") {
                let after = &tail["<p class=\"prose\">".len()..];
                if let Some((inner, _)) = after.split_once("</p>") {
                    let line = visible_text(inner);
                    // A directive is a SENTENCE. A two-word chip is a label, not an instruction.
                    if line.split_whitespace().count() >= 4 {
                        return Some(line);
                    }
                }
                i = at + 1;
            } else {
                i = at + 1;
            }
        }
    }
    None
}

/// **Could this token BE a secret?** — a deliberate, documented narrowing of the fog check's
/// sensitivity.
///
/// A hidden-information surface's secrets are IDENTIFIERS: a card id (`#7`), a board square
/// (`(3,3)`), a hand's committed root (`ab12cd…`), a sealed digest. Its *phrasing* differs per
/// viewer too — "Your piece is picked up", "the buttons name the action and not the cards" — and a
/// pure set-difference cannot tell a per-viewer SENTENCE from a per-viewer SECRET. The first run of
/// this check reported `picked`, `action`, `buttons`, `claims` and `land` as leaks; every one was
/// prose, and a gate that cries wolf gets muted, which is worse than a narrower gate.
///
/// So: a token counts only if it carries a digit, or is long enough to be a digest. The cost is
/// stated plainly rather than hidden — **this check detects DATA-shaped leaks, not prose-shaped
/// ones.** A surface that leaked a secret purely in words would pass it. The tug leak it
/// generalises (`card #3`, `#4 g3w3` in a button label) is data-shaped, as is automatafl's sealed
/// destination and every hand root on the table.
fn is_secret_shaped(token: &str) -> bool {
    token.chars().any(|c| c.is_ascii_digit()) || token.chars().count() >= 12
}

/// The comparable tokens of a rendered page — the things a leak would carry, as a person's eye
/// would group them.
///
/// ⚑ WHITESPACE-SPLIT, not punctuation-split. Splitting on every non-alphanumeric shreds exactly
/// the tokens that ARE the secrets: automatafl's sealed destination `(3,3)` became two
/// one-character fragments and vanished, so the fog check could only ever report vacuity on that
/// game. Sentence punctuation is trimmed off the ends (`move:` ≡ `move`, and the badge brackets
/// `render_text` puts round a pill are not part of its words), but `#` and `()` are STRUCTURE —
/// `#7` is a card and `(3,3)` is a square — so they stay. One-character and word-less tokens are
/// dropped as noise.
fn tokens(text: &str) -> BTreeSet<String> {
    const TRIM: &[char] = &[
        '.', ',', ';', ':', '!', '?', '"', '\'', '…', '·', '—', '–', '[', ']', '`',
    ];
    text.split_whitespace()
        .map(|t| t.trim_matches(TRIM))
        .filter(|t| t.chars().count() >= 2 && t.chars().any(|c| c.is_alphanumeric()))
        .map(|t| t.to_string())
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE HTTP DRIVER
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **The identity the sweep drives as.** `alice` is not an arbitrary name: `catalog_default_host`
/// derives the deployed council's electorate from web usernames and enfranchises exactly `alice`
/// and `bob`, so this is a REAL player of the deployed demo rather than a stranger who can do
/// nothing on a governance surface. (That a stranger's council page is all dead controls was a
/// finding of its own — it is fixed at the source by `CouncilOffering::actions_for`, which now
/// dims for a non-member instead of offering live controls that only refuse.)
const DRIVER: &str = "alice";

fn surface_uri(key: &str, id: &str) -> String {
    format!("/offerings/{key}/session/{id}")
}

fn act_uri(key: &str, id: &str) -> String {
    format!("/offerings/{key}/session/{id}/act")
}

fn cookie(user: &str) -> String {
    format!("dregg_user={user}")
}

/// GET **just the swappable surface fragment** (`X-Fragment: 1`) as `user` — the page's own live
/// region, with no page chrome, no stylesheet and no script to launder a text comparison through.
async fn fragment(app: &Router, key: &str, id: &str, user: &str) -> (StatusCode, String) {
    use axum::body::Body;
    use axum::http::Request;
    use tower::ServiceExt;
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .uri(surface_uri(key, id))
                .header("cookie", cookie(user))
                .header("x-fragment", "1")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8_lossy(&bytes).to_string())
}

/// The first act the page OFFERS AND ENABLES, read off its own form.
fn first_enabled(html: &str) -> Option<common::OfferedAct> {
    common::offered_acts(html).into_iter().find(|a| a.enabled)
}

/// **The first enabled act whose VERB this seat has not played yet**, falling back to the first
/// enabled one.
///
/// ⚑ A multi-round drive that always takes the first enabled act does not explore a game, it
/// re-presses one control. Automatafl paints its board row-major, so the first form on the page is
/// a `select` of the first movable piece — for as many rounds as you care to run. Six landed moves
/// produced six `select`s, the match never reached COMMIT, no seat ever sealed anything, and the
/// fog check could only report that there was no secret to leak. Preferring an unplayed verb walks
/// `select → commit → reveal` on its own, with no knowledge of any game's phase ladder.
fn first_unplayed(html: &str, played: &BTreeSet<String>) -> Option<common::OfferedAct> {
    let acts = common::offered_acts(html);
    acts.iter()
        .find(|a| a.enabled && !played.contains(&a.turn))
        .or_else(|| acts.iter().find(|a| a.enabled))
        .cloned()
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE PROSE PROJECTION (the chat half)
// ─────────────────────────────────────────────────────────────────────────────────────────

/// Every `Pill`'s text in a view tree, in order.
fn pills(node: &ViewNode, out: &mut Vec<String>) {
    match node {
        ViewNode::Pill { text, .. } => out.push(text.clone()),
        ViewNode::Section { children, .. }
        | ViewNode::VStack(children)
        | ViewNode::Row(children)
        | ViewNode::List(children)
        | ViewNode::Table(children)
        | ViewNode::Grid { children, .. } => {
            for c in children {
                pills(c, out);
            }
        }
        ViewNode::Tabs { panels, .. } => {
            for p in panels {
                pills(p, out);
            }
        }
        ViewNode::Host { view: Some(v), .. } => pills(v, out),
        ViewNode::Adept(inner) => pills(inner, out),
        _ => {}
    }
}

/// **Does this pill's information survive the prose projection?**
///
/// Not a substring match on the pill's exact glyph-decorated string — a pill reads
/// `⚑ RE-SUBMIT · round 2` and its prose mirror may legitimately word it differently. What must
/// survive is the pill's INFORMATION, so the test is on its word tokens: every alphanumeric token
/// the pill carries must appear somewhere in `render_text`. A pill made only of symbols (`↺`, `·`)
/// carries no words and cannot be lost.
fn pill_survives(pill: &str, prose: &str) -> bool {
    let want = tokens(&pill.to_lowercase());
    if want.is_empty() {
        return true;
    }
    let have = tokens(&prose.to_lowercase());
    want.iter().all(|t| have.contains(t))
}

/// The prose-parity verdict for one offering, driven on a peer host exactly as a chat transport
/// drives it: open, render FOR a viewer, take the first enabled affordance, render again.
///
/// Uses `OfferingHost` directly (not HTTP) because the projection under test IS
/// `deos_view::text::render_text` over the offering's own `ViewNode` — the function Telegram's and
/// WeChat's backends call. The web renderer is not in this path and cannot fix it.
fn prose_parity(host: &mut OfferingHost, key: &str, viewer: &DreggIdentity) -> (bool, String) {
    let id = SessionId::new(format!("prose-{key}"));
    if let Err(e) = host.ensure_open(key, &id) {
        return (
            false,
            format!("the offering would not open for a chat viewer: {e}"),
        );
    }
    let mut worst: Option<String> = None;
    for step in ["on open", "after one turn"] {
        let Some(surface) = host.render_for(key, &id, viewer) else {
            return (false, format!("{step}: the offering rendered nothing"));
        };
        let mut found = Vec::new();
        pills(surface.view(), &mut found);
        let prose = render_text(surface.view());
        for pill in &found {
            if !pill_survives(pill, &prose) {
                worst.get_or_insert(format!(
                    "{step}: the pill `{pill}` reaches the web page and NOTHING of it reaches \
                     `render_text`, so a Telegram/WeChat reader never learns it \
                     ({} pills on this surface)",
                    found.len()
                ));
                break;
            }
        }
        if worst.is_some() {
            break;
        }
        if step == "on open" {
            // Advance one turn so the check also covers mid-game pills (phase ladders, standings).
            let Some(next) = host
                .actions_for(key, &id, viewer)
                .unwrap_or_default()
                .into_iter()
                .find(|a| a.enabled)
            else {
                break;
            };
            let _ = host.advance(key, &id, next, viewer.clone());
        }
    }
    match worst {
        Some(detail) => (false, detail),
        None => (
            true,
            "every pill's words reach the prose projection".to_string(),
        ),
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE SWEEP
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **The live catalog IS the sweep's input.** Both polarities against the shared contract, so a new
/// offering is covered the day it lands and one cannot be quietly dropped from the harness either.
#[tokio::test]
async fn the_harness_enumerates_the_whole_live_catalog() {
    dreggnet_catalog::publish_pinned_descent_day().expect("the pinned published round verifies");
    let (_router, state) = dreggnet_web::make_app_parts();
    let mut live: Vec<String> = state.list_offerings().into_iter().map(|o| o.key).collect();
    live.sort();
    let mut contract: Vec<String> = dreggnet_catalog::CATALOG_KEYS
        .iter()
        .map(|k| k.to_string())
        .collect();
    contract.sort();
    assert_eq!(
        live, contract,
        "the deployed router's own registry IS `dreggnet_catalog::CATALOG_KEYS` — the flow harness \
         sweeps whatever this returns, so a divergence here means the sweep is covering a \
         different catalog than the one that ships"
    );

    // ⚑ AND THE SHELF IS A SUBSET OF THE SWEEP. The curated public list is what a stranger is
    // shown; the sweep is the whole registry. This is the one relationship that must hold between
    // them — advertising a key the harness never drives would leave the shelf itself unchecked.
    for key in dreggnet_catalog::SHIPPED_KEYS {
        assert!(
            live.iter().any(|k| k == key),
            "`SHIPPED_KEYS` advertises `{key}`, which the deployed router does not register — the \
             shelf would point strangers at an offering nothing drives: {live:?}"
        );
    }
}

/// **THE HARNESS.** Drive every registered offering through the deployed router and record every
/// invariant. Reports ALL failures in one table.
#[tokio::test]
async fn every_offering_survives_being_driven_through_its_own_flow() {
    dreggnet_catalog::publish_pinned_descent_day().expect("the pinned published round verifies");
    let (router, state) = dreggnet_web::make_app_parts();
    let app = common::guard(router);
    let keys: Vec<String> = state.list_offerings().into_iter().map(|o| o.key).collect();
    assert!(!keys.is_empty(), "the deployed catalog registers nothing");

    // A peer host answers the two questions the HTTP surface cannot: whether an offering DECLARES
    // hidden information (a property of the offering, answered without a session), and what its
    // `ViewNode` tree projects to in prose. It is built by the same `dreggnet_catalog` registrar
    // the deployed catalog uses, so it is the same offerings.
    let mut peer = dreggnet_web::demo_host();
    let chat_viewer = dreggnet_web::web_identity("flowchat");

    let mut rows: Vec<Row> = Vec::new();
    for key in &keys {
        let mut row = Row::new(key);
        let id = format!("flow-{key}");

        // ── OPEN: read the page a stranger lands on.
        let (status, before) = fragment(&app, key, &id, DRIVER).await;
        if status != StatusCode::OK {
            row.fail_rest(&format!(
                "the offering would not even open over the deployed router: HTTP {status} — \
                 body: {}",
                &before[..before.len().min(300)]
            ));
            rows.push(row);
            continue;
        }
        let before_text = visible_text(&before);

        // ── (a) A DIRECTIVE EXISTS.
        match directive_of(&before) {
            Some(line) => row.record(INV_DIRECTIVE, true, format!("“{line}”")),
            None => row.record(
                INV_DIRECTIVE,
                false,
                format!(
                    "no `accent` plaque with a leading sentence — the page states what the state \
                     IS and never what to do NOW. The shared skin already promotes that sentence \
                     (serif lead on a violet rule); this surface emits none. First words the page \
                     shows: “{}”",
                    before_text.chars().take(140).collect::<String>()
                ),
            ),
        }

        // ── (b) NO DEBUG DUMP IN USER-FACING TEXT.
        let dumps = debug_dump_hits(&before_text);
        row.record(
            INV_NO_DEBUG,
            dumps.is_empty(),
            if dumps.is_empty() {
                "no `{:?}`-shaped text on the opened page".to_string()
            } else {
                format!("a Debug dump reaches the reader: {dumps:?}")
            },
        );

        // ── (c) STATE SURVIVES THE PROSE PROJECTION (the chat half).
        let (held, detail) = prose_parity(&mut peer, key, &chat_viewer);
        row.record(INV_PROSE_PARITY, held, detail);

        // ── (d) AN OFFERED ACT CAN ACTUALLY LAND, and (e) THE RENDER CHANGES.
        match first_enabled(&before) {
            None => {
                let offered = common::offered_acts(&before).len();
                row.record(
                    INV_ACT_LANDS,
                    false,
                    format!(
                        "the opened page offers NO enabled act ({offered} affordance(s) rendered, \
                         every one dimmed) — a player who opens this has nothing they can press"
                    ),
                );
                // Counted ONCE, at `act-lands`. There is no turn to land, so there is no state
                // change owed — and this is not a silent skip: the cell above is already red and
                // names the same cause.
                row.not_applicable(
                    INV_STATE_VISIBLE,
                    "no act could be taken (see this row's `act-lands` failure), so no state \
                     change was owed",
                );
            }
            Some(act) => {
                let (status, response) =
                    common::post_act(&app, &act_uri(key, &id), &act.turn, act.arg, DRIVER).await;
                let refused = response.contains("class=\"notice refused\"");
                let landed = response.contains("Turn committed") && !refused;
                row.record(
                    INV_ACT_LANDS,
                    landed,
                    if landed {
                        format!("`{}`/{} — offered and accepted", act.turn, act.arg)
                    } else {
                        format!(
                            "the page OFFERED `{}`/{} (label “{}”) and the executor did not land \
                             it — HTTP {status}. A dead affordance. Notice: “{}”",
                            act.turn,
                            act.arg,
                            act.label,
                            first_notice(&response)
                        )
                    },
                );

                let (_, after) = fragment(&app, key, &id, DRIVER).await;
                let after_text = visible_text(&after);
                let changed = after_text != before_text;
                if landed {
                    row.record(
                        INV_STATE_VISIBLE,
                        changed,
                        if changed {
                            format!(
                                "the page's visible text moved after `{}`/{}",
                                act.turn, act.arg
                            )
                        } else {
                            format!(
                                "`{}`/{} LANDED a real turn and the page re-rendered with \
                                 BYTE-IDENTICAL visible text — a player cannot tell anything \
                                 happened. ({} chars of prose, unchanged.)",
                                act.turn,
                                act.arg,
                                after_text.len()
                            )
                        },
                    );
                } else {
                    // ⚑ NOT a pass. Nothing committed, so nothing was owed — and calling that a
                    // pass would launder a red into a green on the strength of a DIFFERENT
                    // failure. The `act-lands` cell above already carries it, loudly.
                    row.not_applicable(
                        INV_STATE_VISIBLE,
                        "no turn landed (see this row's `act-lands` failure), so no state change \
                         was owed",
                    );
                }
            }
        }

        // ── (f) FOG, for the offerings that declare hidden information.
        match peer.hidden_information(key) {
            Some(true) => {
                let (held, detail) = fog_check(&app, &mut peer, key).await;
                row.record(INV_FOG, held, detail);
            }
            Some(false) => row.not_applicable(
                INV_FOG,
                "the offering declares `hidden_information() == false`",
            ),
            None => row.record(
                INV_FOG,
                false,
                "the peer host does not know this key — the two catalogs have drifted",
            ),
        }

        rows.push(row);
    }

    // ── The report, plus THE SHIPPED TIER. Every non-PASS cell on an advertised offering is
    //    called out again: the same allowance costs more on the shelf a stranger is shown than on
    //    an experiment nobody is pointed at. `SHIPPED_KEYS` is READ, never re-typed, so re-listing
    //    an offering promotes its row here with no edit to this file.
    let mut table = render_table(&rows);
    let mut shelf = String::new();
    for key in dreggnet_catalog::SHIPPED_KEYS {
        let Some(row) = rows.iter().find(|r| r.key == key) else {
            let _ = write!(
                shelf,
                "\n  {key}: ON THE SHELF AND NOT SWEPT — `SHIPPED_KEYS` advertises a key the \
                 deployed router does not register"
            );
            continue;
        };
        for invariant in INVARIANTS {
            match row.verdict(invariant) {
                Verdict::Fail => {
                    let _ = write!(shelf, "\n  {key}/{invariant}: FAIL — on the shelf.");
                }
                Verdict::Exempt => {
                    let _ = write!(
                        shelf,
                        "\n  {key}/{invariant}: allowed, ON THE SHELF — a documented defect on a \
                         surface strangers are actually sent to."
                    );
                }
                _ => {}
            }
        }
    }
    let _ = write!(
        table,
        "\nSHIPPED TIER ({}){}\n",
        dreggnet_catalog::SHIPPED_KEYS.join(" · "),
        if shelf.is_empty() {
            " — every advertised offering is clean on every invariant.".to_string()
        } else {
            shelf
        }
    );
    println!("{table}");

    // ── Stale allowances are failures of their own.
    let mut stale = Vec::new();
    for exemption in EXEMPTIONS {
        let Some(row) = rows.iter().find(|r| r.key == exemption.key) else {
            stale.push(format!(
                "  {}/{}: no such offering in the live catalog — delete the allowance",
                exemption.key, exemption.invariant
            ));
            continue;
        };
        if row.verdict(exemption.invariant) == Verdict::Pass {
            stale.push(format!(
                "  {}/{}: PASSES now — delete the allowance (it was: {})",
                exemption.key, exemption.invariant, exemption.reason
            ));
        }
    }

    let failures: Vec<String> = rows
        .iter()
        .flat_map(|row| {
            INVARIANTS.iter().filter_map(move |invariant| {
                (row.verdict(invariant) == Verdict::Fail).then(|| {
                    format!(
                        "  {}/{invariant}: {}",
                        row.key,
                        row.cells
                            .get(invariant)
                            .map(|c| c.detail.as_str())
                            .unwrap_or("")
                    )
                })
            })
        })
        .collect();

    assert!(
        failures.is_empty() && stale.is_empty(),
        "{table}\n{} offering×invariant failure(s):\n{}\n{}{}",
        failures.len(),
        failures.join("\n"),
        if stale.is_empty() {
            String::new()
        } else {
            format!(
                "{} STALE ALLOWANCE(S):\n{}\n",
                stale.len(),
                stale.join("\n")
            )
        },
        "\nEach line names the offering, the invariant, and the offending text. Fix it, or record \
         a named allowance in `EXEMPTIONS` with the design work it actually needs."
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE DETECTORS' OWN TEETH — a checker that has never fired is not known to work
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **`no-debug` passes on all 23 offerings, so the detector itself must be shown to bite.** These
/// are the shapes a Rust `Debug` impl produces, and the prose shapes it must NOT mistake for one —
/// `format!("seat {s:?}")` over a fieldless enum prints `seat A`, which is fine prose and is
/// exactly what `dregg-multiway-tug`'s surface does.
#[test]
fn the_debug_dump_detector_bites_and_does_not_false_alarm() {
    for dump in [
        "the winner was Bid { amount: 500, sealed: true }",
        "actor DreggIdentity(\"7892fae5\") holds the seat",
        "the sealed move was Some(Move { x: 3, y: 4 })",
        "root [12, 255, 7, 88, 3] committed",
        "roster [\"aria\", \"bram\", \"cyra\"] admitted",
    ] {
        assert!(
            !debug_dump_hits(dump).is_empty(),
            "a Debug dump must be caught: {dump}"
        );
    }
    for prose in [
        "Seat A has cut a Secret and it is FACE UP. Choose the side you take.",
        "The automaton stands at (3,4). Nobody moves it directly.",
        "goals A (0,0)·(10,0) · seat B · 2 steps from a goal",
        "Fund the archive (42 votes) · Ratify the charter (7)",
        "light ██████████████████░░░░░░░░ 18/26 · pack ██░░░░ 2/6",
        "Forge the Ember Cloak (3/3 inputs) — 12◈",
    ] {
        assert!(
            debug_dump_hits(prose).is_empty(),
            "ordinary surface prose must NOT be flagged: {prose} → {:?}",
            debug_dump_hits(prose)
        );
    }
}

/// **The directive detector reads the CSS's `>`, not "somewhere inside".** The first pass matched
/// any `<p class="prose">` inside an `accent` plaque and handed back a table row three levels down
/// — a page with no directive at all passed. Both polarities are pinned here.
#[test]
fn the_directive_detector_wants_a_direct_child_sentence() {
    let real = "<section class=\"deos-section tag-accent\"><h2>Your next move</h2>\
                <div class=\"deos-row\"><span class=\"pill\">FORMING</span></div>\
                <p class=\"prose\">Claim one of the four roles below to seat yourself.</p>\
                </section>";
    assert_eq!(
        directive_of(real).as_deref(),
        Some("Claim one of the four roles below to seat yourself."),
        "a sibling pill row does not disqualify the first DIRECT-child paragraph — the CSS \
         selector is `> .prose:first-of-type`, and a `<div>` is not a `<p>`"
    );

    let nested_only = "<section class=\"deos-section tag-accent\"><h2>LFG board</h2>\
                       <div class=\"deos-list\"><p class=\"prose\">aria: looking for a healer</p>\
                       </div></section>";
    assert_eq!(
        directive_of(nested_only),
        None,
        "a row of DATA nested inside the plaque is not a directive, however early it appears"
    );

    let too_short = "<section class=\"deos-section tag-accent\"><h2>Grain</h2>\
                     <p class=\"prose\">turns 0/1000</p></section>";
    assert_eq!(
        directive_of(too_short),
        None,
        "a state chip is not an instruction"
    );
}

/// The page-reading helpers do what their names claim — otherwise every invariant above is
/// measuring the wrong string.
#[test]
fn the_page_readers_read_what_a_person_reads() {
    let html = "<div class=\"notice ok\">Turn committed</div>\
                <form class=\"affordance\"><input type=\"hidden\" name=\"turn\" value=\"gift\">\
                <input class=\"arg\" type=\"number\" name=\"arg\" value=\"2\">\
                <button type=\"submit\">Gift Ember Cloak &amp; wait</button></form>\
                <form class=\"affordance dimmed\"><input type=\"hidden\" name=\"turn\" value=\"sell\">\
                <input class=\"arg\" type=\"number\" name=\"arg\" value=\"1\" disabled>\
                <button type=\"submit\" disabled>Sell</button></form>";

    // Hidden inputs never reach the reader — which is what keeps `state-visible` honest against a
    // per-request form token.
    let text = visible_text(html);
    assert!(text.contains("Turn committed") && text.contains("Gift Ember Cloak & wait"));
    assert!(!text.contains("gift") && !text.contains("value="));

    let acts = common::offered_acts(html);
    assert_eq!(acts.len(), 2);
    assert_eq!(
        (acts[0].turn.as_str(), acts[0].arg, acts[0].enabled),
        ("gift", 2, true)
    );
    assert_eq!(
        (acts[1].turn.as_str(), acts[1].arg, acts[1].enabled),
        ("sell", 1, false)
    );
    assert_eq!(
        first_enabled(html).map(|a| a.turn),
        Some("gift".to_string()),
        "a dimmed row is never the act the harness fires — pressing one is a real refusal"
    );
    assert_eq!(control_labels(html), ["Gift Ember Cloak & wait", "Sell"]);

    // The prose half drops exactly the labels and keeps everything else — the asymmetry the fog
    // check is built on.
    let prose = visible_text_sans_controls(html);
    assert!(prose.contains("Turn committed"));
    assert!(
        !prose.contains("Gift Ember Cloak") && !prose.contains("Sell"),
        "a control label is not prose: {prose}"
    );
}

/// The notice banner a POST response carries (the landed receipt or the refusal), for a message.
fn first_notice(html: &str) -> String {
    for cls in ["notice refused", "notice ok"] {
        let marker = format!("<div class=\"{cls}\" role=\"status\">");
        if let Some((_, rest)) = html.split_once(&marker) {
            if let Some((inner, _)) = rest.split_once("</div>") {
                return visible_text(inner);
            }
        }
    }
    "(no notice rendered)".to_string()
}

/// **THE FOG CHECK** — the tug leak, generalised to every hidden-information offering.
///
/// Three browsers on ONE table: `flowseata` and `flowseatb` each land a move (claiming the two
/// seats); `flowwatch` never acts and holds no seat. A peer host is driven with the EXACT same
/// `(turn, arg, identity)` triples, which keeps it in lockstep and supplies the one thing HTTP
/// cannot: the offering's OWN viewer-blind `render()` — its statement of what is public.
///
/// A seat's SECRET is then defined without any per-game knowledge, **per step**:
///
/// ```text
/// secret(A, t) = tokens(A's PROSE at t) \ tokens(B's PROSE at t) \ tokens(public, ANY step)
/// ```
///
/// — what A can read at that moment that is neither their opponent's view nor anything the
/// offering's own viewer-blind projection ever says. Personalisation ("(you)", "Your hand") is
/// symmetric and cancels; A's cards do not.
///
/// The two window choices are both load-bearing, and both were paid for by a wrong first answer:
///
/// * **the SEAT comparison is PER STEP**, because a commit-reveal secret is temporary BY DESIGN.
///   Unioning a seat's pages over the whole drive folds the post-reveal frame — where automatafl's
///   move is public and appears on both pages — back over the pre-reveal frame where it was
///   sealed, and the secret vanishes.
/// * **the PUBLIC subtraction spans EVERY step**, because ordinary English drifts between frames
///   and a word the public projection says at any point in this match is not a secret at any other.
/// * **a seat's secrets are read from its PROSE, never its control labels**
///   ([`visible_text_sans_controls`]) — a label's presence tracks whose turn it is, which made the
///   word "put", out of tug's `Secret — put a favor face down`, look private on the first run.
///
/// The gate:
///
/// * **no token of `secret(A, t)` or `secret(B, t)` may appear on the watcher's page at step `t`** —
///   checked over the watcher's WHOLE visible text, controls included, so a leak through a CONTROL
///   LABEL (exactly where tug's lived) is caught, and is REPORTED as a label leak;
/// * **some step must give each seat a NON-EMPTY secret** — the non-vacuity tooth, and also the
///   opponent-direction tooth: if B's page leaked A's private content, those tokens would fall out
///   of `secret(A, t)` at every step and this fires.
async fn fog_check(app: &Router, peer: &mut OfferingHost, key: &str) -> (bool, String) {
    /// How many alternating rounds the two seats play before the fog is judged. ⚑ ONE is not
    /// enough: automatafl's first move per seat is a `select`, which seals nothing, so a one-round
    /// drive found both seats' secret sets EMPTY and could only report vacuity. A seat's secret has
    /// to EXIST before "does the watcher see it" means anything — hence three rounds AND
    /// [`first_unplayed`], which is what actually walks `select → commit → reveal`.
    const ROUNDS: usize = 3;

    let id = format!("fog-{key}");
    let sid = SessionId::new(id.clone());
    if let Err(e) = peer.ensure_open(key, &sid) {
        return (
            false,
            format!("the peer host would not open the table: {e}"),
        );
    }
    let seats = ["flowseata", "flowseatb"];
    let watcher = "flowwatch";

    /// One three-viewer frame: the step's name, each seat's PROSE tokens, and the watcher's whole
    /// page (controls included — that is where tug's leak lived) plus its labels on their own.
    struct Frame {
        step: String,
        seat: [BTreeSet<String>; 2],
        /// Whether each seat had actually CLAIMED by this frame. ⚑ An unclaimed "seat" is being
        /// served the public/claim projection, so the differential would call that projection's
        /// own prose ("the buttons name the action and not the cards") a secret of the seat that
        /// has not sat down. A viewer holding no seat HAS no secrets, by definition.
        seated: [bool; 2],
        watch_text: String,
        watch_labels: Vec<String>,
        watch_enabled: usize,
    }

    fn frame(step: String, a: &str, b: &str, watch: &str, seated: [bool; 2]) -> Frame {
        Frame {
            step,
            seat: [
                tokens(&visible_text_sans_controls(a).to_lowercase()),
                tokens(&visible_text_sans_controls(b).to_lowercase()),
            ],
            seated,
            watch_text: visible_text(watch),
            watch_labels: control_labels(watch),
            watch_enabled: common::offered_acts(watch)
                .into_iter()
                .filter(|act| act.enabled)
                .count(),
        }
    }

    let mut frames: Vec<Frame> = Vec::new();
    let mut public: BTreeSet<String> = BTreeSet::new();
    let mut played: [BTreeSet<String>; 2] = [BTreeSet::new(), BTreeSet::new()];
    let mut landed: Vec<String> = Vec::new();

    let (_, a0) = fragment(app, key, &id, seats[0]).await;
    let (_, b0) = fragment(app, key, &id, seats[1]).await;
    let (_, w0) = fragment(app, key, &id, watcher).await;
    frames.push(frame(
        "before either seat acted".into(),
        &a0,
        &b0,
        &w0,
        [false, false],
    ));
    if let Some(surface) = peer.render(key, &sid) {
        public.extend(tokens(&render_text(surface.view()).to_lowercase()));
    }

    for round in 1..=ROUNDS {
        for (i, user) in seats.iter().enumerate() {
            let (_, own) = fragment(app, key, &id, user).await;
            // A seat with nothing to press this round simply passes — only a table where NEITHER
            // seat ever landed anything is a broken drive.
            let Some(act) = first_unplayed(&own, &played[i]) else {
                continue;
            };
            let (_, response) =
                common::post_act(app, &act_uri(key, &id), &act.turn, act.arg, user).await;
            if !response.contains("Turn committed") {
                continue;
            }
            played[i].insert(act.turn.clone());
            landed.push(format!(
                "{}`{}`",
                if i == 0 { "A:" } else { "B:" },
                act.turn
            ));
            // The peer host is only useful while it is in LOCKSTEP with the router — its whole job
            // is to supply the viewer-blind public projection OF THIS STATE. A desync is reported
            // as a broken check, never as a pass.
            match peer.advance(
                key,
                &sid,
                Action::new(act.label.clone(), &act.turn, act.arg, true),
                dreggnet_web::web_identity(user),
            ) {
                None => {
                    return (
                        false,
                        "the peer host has no such session — its public baseline cannot be trusted"
                            .to_string(),
                    );
                }
                Some(Outcome::Refused(why)) => {
                    return (
                        false,
                        format!(
                            "the peer host REFUSED the very move the router landed (`{}`/{}): \
                             {why} — the public baseline would then be from a different state, so \
                             this check is reported BROKEN rather than passed",
                            act.turn, act.arg
                        ),
                    );
                }
                Some(_) => {}
            }
            if let Some(surface) = peer.render(key, &sid) {
                public.extend(tokens(&render_text(surface.view()).to_lowercase()));
            }
            let (_, a) = fragment(app, key, &id, seats[0]).await;
            let (_, b) = fragment(app, key, &id, seats[1]).await;
            let (_, w) = fragment(app, key, &id, watcher).await;
            let seat = if i == 0 { "A" } else { "B" };
            frames.push(frame(
                format!(
                    "after seat {seat} played `{}`/{} (round {round})",
                    act.turn, act.arg
                ),
                &a,
                &b,
                &w,
                [!played[0].is_empty(), !played[1].is_empty()],
            ));
        }
    }

    if landed.is_empty() {
        return (
            false,
            "neither seat could land a single offered act, so the table never reached a state \
             where anything was hidden"
                .to_string(),
        );
    }

    // `secret(X, t)` — see this function's doc for why the SEAT half is per-frame, the PUBLIC half
    // spans every frame, and only a token that is SECRET-SHAPED counts.
    let secret = |f: &Frame, mine: usize| -> BTreeSet<String> {
        if !f.seated[mine] {
            return BTreeSet::new();
        }
        f.seat[mine]
            .difference(&f.seat[1 - mine])
            .filter(|t| !public.contains(*t) && is_secret_shaped(t))
            .cloned()
            .collect()
    };

    // ⚑ QA-SWEEP FINDING, MECHANISED (docs/reference/UX-QA-SWEEP-2026-07-26.md §2). Both game
    // surfaces TELL a seatless viewer "every control is inert" and then serve them 121 cell
    // buttons carrying no `disabled` attribute; a reader proved the claim false by pressing one
    // and changing their seat, their hand and the turn counter. Once BOTH seats are taken there is
    // no honest reading under which a viewer holding neither may act, so this needs no prose
    // matching and no game knowledge: count the enabled controls the watcher is served.
    //
    // Deliberately NOT checked before both seats are taken: tug's claim surface offers a
    // prospective claimant real controls on purpose ("the first move you land CLAIMS seat B"), and
    // those DO land. Only a table with no seat left to claim makes the offer a lie.
    if let Some(f) = frames
        .iter()
        .rev()
        .find(|f| f.seated[0] && f.seated[1] && f.watch_enabled > 0)
    {
        return (
            false,
            format!(
                "both seats are taken and a viewer holding NEITHER is still served {} ENABLED \
                 control(s) {} — every one of them is a press the executor must refuse. A control \
                 that can only refuse is a lie the page tells before the substrate gets a say; \
                 render it `disabled` (the cap tooth SHOWN, not hidden). Labels served: {:?}",
                f.watch_enabled,
                f.step,
                f.watch_labels.iter().take(3).collect::<Vec<_>>()
            ),
        );
    }

    let mut widest = [0usize, 0usize];
    for f in &frames {
        let secrets = [secret(f, 0), secret(f, 1)];
        for (i, own) in secrets.iter().enumerate() {
            widest[i] = widest[i].max(own.len());
            let leaked: Vec<&String> = own
                .iter()
                .filter(|t| tokens(&f.watch_text.to_lowercase()).contains(*t))
                .take(4)
                .collect();
            if leaked.is_empty() {
                continue;
            }
            let via_label = f.watch_labels.iter().any(|l| {
                let lt = tokens(&l.to_lowercase());
                leaked.iter().any(|t| lt.contains(*t))
            });
            return (
                false,
                format!(
                    "a viewer holding NO seat read seat {}'s private token(s) {leaked:?} {}{} — \
                     this offering declares hidden information and a watcher is not entitled to \
                     that. (Drive: {}.)",
                    if i == 0 { "A" } else { "B" },
                    f.step,
                    if via_label {
                        " ⚑ THROUGH A CONTROL LABEL (not the prose sections — exactly where tug's \
                         leak lived, and where a prose-only fog test cannot look)"
                    } else {
                        " (in the page prose)"
                    },
                    landed.join(" ")
                ),
            );
        }
    }

    // ⚑ NON-VACUITY, and the opponent tooth in the same assertion. If seat B's page leaked seat
    // A's private content, those tokens fall OUT of `secret(A, t)` at every frame — so an
    // always-empty secret set is either "this offering hides nothing after all" or "each seat
    // already reads the other's", and both mean this gate cannot bite. Either way it is a failure,
    // never a quiet pass.
    if widest[0] == 0 || widest[1] == 0 {
        return (
            false,
            format!(
                "VACUOUS or LEAKING TO THE OPPONENT: `hidden_information()` is declared true, but \
                 across {} frames the WIDEST secret-shaped private-token set was {} for seat A and \
                 {} for seat B — nothing data-shaped that seat can read is absent from both the \
                 opponent's page and the offering's own public projection. (Drive: {}.)",
                frames.len(),
                widest[0],
                widest[1],
                landed.join(" ")
            ),
        );
    }

    (
        true,
        format!(
            "across {} frames, a seatless viewer reads none of the up-to-{} tokens private to seat \
             A or the up-to-{} private to seat B — controls included. (Drive: {}.)",
            frames.len(),
            widest[0],
            widest[1],
            landed.join(" ")
        ),
    )
}
