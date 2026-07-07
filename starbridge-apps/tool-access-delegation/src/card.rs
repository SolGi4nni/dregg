//! # tool-access-delegation — the UI as a deos-view CARD (a `deos.ui.*` view-tree, AX4).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by shipping
//! its surface as a **renderer-independent card** — a serializable `deos.ui.*` element-tree
//! ([`deos_view::ViewNode`] in the renderer crate). The SAME tree renders three ways (the
//! renderer-independence seam): native gpui pixels in the cockpit, a browser-loadable HTML
//! document, and a discord embed — all from this one piece of DATA. See
//! `deos-view/src/{render,web,discord}.rs` and `docs/reference/deos-view.md`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native elephants, so it is
//! a STANDALONE workspace EXCLUDED from the repo-root workspace. A starbridge-app must never
//! depend on it — that would feature-unify the elephants onto the main build. So the app's
//! contribution is the **view-tree JSON** (this module): pure `serde_json`, no elephant. The
//! deos world's renderers consume it; this module owns the card definition and proves it is
//! well-formed.
//!
//! ## The card shape — a rich, live RATE-LIMITED MANDATE surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view vocabulary
//! (`section` / `pill` / `gauge` / `progress` / `breadcrumb` / `divider` / `icon`), so the
//! object-capability story — *a delegate holds a NARROWLY-BOUNDED, RATE-LIMITED, TIME-BOUNDED
//! invoke capability* — is VISIBLE at a glance:
//!
//!   - a **status header** — the app name + a LIVE `pill` ([`status_pill`]) reading
//!     [`CALLS_MADE_SLOT`](crate::CALLS_MADE_SLOT) and naming the mandate state as a WORD
//!     (`ACTIVE` / `RATE-LIMITED` at the ceiling; `EXPIRED` is the deadline bar's story), and
//!     a `breadcrumb` of the whole
//!     delegation lifecycle (granted → delegated → exercising → revoked) with the current step
//!     marked;
//!   - a **"Mandate" `section`** surfacing the LIVE rate budget: a `gauge` bound to
//!     [`CALLS_MADE_SLOT`](crate::CALLS_MADE_SLOT) over the granted ceiling — the killer
//!     visual, it FILLS as the worker spends its budget and is FULL the instant the rate
//!     ceiling is reached (the bounded authority made legible); a deadline `progress`
//!     (time-remaining in the granted window); and `bind`s on the tool SCOPE
//!     ([`TOOL_ID_SLOT`](crate::TOOL_ID_SLOT)), the calls used
//!     ([`CALLS_MADE_SLOT`](crate::CALLS_MADE_SLOT)), the rate ceiling
//!     ([`RATE_LIMIT_SLOT`](crate::RATE_LIMIT_SLOT)), and the deadline
//!     ([`DEADLINE_SLOT`](crate::DEADLINE_SLOT)) — each a fine-grained signal that re-reads the
//!     live value (the SAME witnessed read a native `bind` closure makes), so the surface
//!     advances when an `exercise` turn commits;
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle method
//!     (`grant` / `exercise` / `delegate` / `revoke`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT cap-gated verified turn a click fires through the
//!     [`invoke()`](crate::service) front door.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_GRANT`](crate::service::METHOD_GRANT), …) so the card and the service cell speak
//! the same delegation lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_DELEGATE, METHOD_EXERCISE, METHOD_GRANT, METHOD_REVOKE};
use crate::{CALLS_MADE_SLOT, DEADLINE_SLOT, RATE_LIMIT_SLOT, TOOL_ID_SLOT};

/// The rate-budget gauge's denominator — the granted invocation ceiling a representative
/// mandate carries (the [`register_deos`](crate::register_deos) seed grants `rate_limit = 8`),
/// so a fully-spent mandate FILLS the gauge. As the worker meters calls the bar climbs toward
/// this ceiling; at `calls_made == rate_limit` the budget is exhausted (the bounded authority).
const RATE_GAUGE_MAX: u64 = 8;

/// The deadline window (`max`) of the time-remaining `progress` — a representative granted
/// expiry height (the Lean `demoGrant` deadline is `100`).
const DEADLINE_WINDOW: u64 = 100;

/// The representative time-remaining (`value`) of the deadline `progress` — heights left in the
/// granted window before the mandate EXPIRES (the `FieldGteHeight(deadline)` tooth bites).
const DEADLINE_REMAINING: u64 = 64;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a word +
/// color via `cases` (the first `{value,label,tag}` matching the slot wins). `text`/`tag` are
/// the static fallback (discord, or no match).
fn pill_live(slot: u8, label: &str, tag: &str, cases: Value) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag, "slot": slot, "cases": cases } })
}

/// A `deos.ui.icon` node — a glyph indicator tinted by `tag`.
fn icon(glyph: &str, tag: &str) -> Value {
    json!({ "kind": "icon", "props": { "glyph": glyph, "tag": tag } })
}

/// A `deos.ui.divider` node — a full-width groove rule.
fn divider() -> Value {
    json!({ "kind": "divider", "props": {} })
}

/// A `deos.ui.row` node — a horizontal flex of children.
fn row(children: Vec<Value>) -> Value {
    json!({ "kind": "row", "props": {}, "children": children })
}

/// A `deos.ui.section` node — a titled, bordered container.
fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix and a display
/// `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"` grouped digits / `"raw"` plain)
/// so an opaque id/amount paints short + friendly. `adept` tags a dev-y row (e.g. a raw block
/// height duplicating a friendlier bar) hidden in the simple projection, revealed in the adept
/// "see the bones" view.
fn bind(slot: u8, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode read of
/// the LIVE slot off the ledger; no bind cursor).
fn gauge(slot: u8, max: u64, label: &str) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label } })
}

/// A `deos.ui.progress` node — a STATIC (literal-valued) progress bar (`value / max`).
fn progress(value: u64, max: u64, label: &str) -> Value {
    json!({ "kind": "progress", "props": { "value": value, "max": max, "label": label } })
}

/// A `deos.ui.breadcrumb` node — the lifecycle path; the `active` step is marked `›`.
fn breadcrumb(steps: &[&str], active: usize) -> Value {
    let items: Vec<Value> = steps
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let label = if i == active {
                format!("› {s}")
            } else {
                s.to_string()
            };
            json!({ "label": label })
        })
        .collect();
    json!({ "kind": "breadcrumb", "props": { "items": items } })
}

/// A `deos.ui.button` node carrying its affordance payload `onClick = {turn, arg}`.
fn button(label: &str, turn: &str, arg: i64) -> Value {
    json!({
        "kind": "button",
        "props": { "label": label, "onClick": { "turn": turn, "arg": arg } }
    })
}

/// An action row — an `icon` + a lifecycle `button` (the verified-turn affordance). The `turn`
/// is the [`service`](crate::service) method symbol the click routes through `invoke()`.
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// The mandate's representative status `pill` — the live-state badge named as a WORD:
///
///   - `ACTIVE` (`good`) — budget remains AND the deadline is in the future (the worker may
///     meter a call);
///   - `RATE-LIMITED` (`warn`) — `calls_made == rate_limit` (the granted budget is spent);
///   - `EXPIRED` (`bad`) — the granted deadline has passed (`FieldGteHeight(deadline)` refuses).
///
/// The seeded mandate is granted with budget remaining and an in-window deadline, so the card
/// surfaces the representative `ACTIVE` state; the live `gauge` + the deadline `progress` show
/// HOW CLOSE to the `RATE-LIMITED` / `EXPIRED` edges the mandate is.
///
/// The pill is LIVE: it reads [`CALLS_MADE_SLOT`](crate::CALLS_MADE_SLOT) and flips to
/// `RATE-LIMITED` (`warn`) the instant the meter reaches the granted ceiling
/// ([`RATE_GAUGE_MAX`]); otherwise the `ACTIVE` (`good`) fallback shows. (`EXPIRED` is
/// height-relative — not a single-slot value — so it stays the deadline `progress` bar's story.)
fn status_pill() -> Value {
    pill_live(
        CALLS_MADE_SLOT,
        "ACTIVE",
        "good",
        json!([
            { "value": RATE_GAUGE_MAX, "label": "RATE-LIMITED", "tag": "warn" },
        ]),
    )
}

/// **The tool-access-delegation card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live rate-limited-mandate surface: a status header (name + [`ACTIVE`](status_pill)
/// pill + delegation-lifecycle breadcrumb), a "Mandate" section surfacing the LIVE rate-budget
/// gauge (`calls_made / rate_limit` — the bounded authority made visible), the deadline
/// time-remaining progress, and the tool / calls-used / rate-ceiling / deadline binds, and an
/// "Actions" section of the four icon-labelled lifecycle buttons. Renderer-independent DATA:
/// hand it to any `deos-view` renderer (native / web / discord) to paint the SAME card. The
/// button `turn` names are the [`service`](crate::service) method symbols.
pub fn mandate_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            row(vec![text("Tool Access Delegation"), status_pill()]),
            breadcrumb(&["Granted", "Delegated", "Exercising", "Revoked"], 2),
            divider(),
            section("Mandate", "genuine", vec![
                gauge(CALLS_MADE_SLOT, RATE_GAUGE_MAX, "rate budget "),
                progress(DEADLINE_REMAINING, DEADLINE_WINDOW, "time remaining "),
                bind(TOOL_ID_SLOT,    "tool · ", "id", false),
                bind(CALLS_MADE_SLOT, "calls used · ", "raw", false),
                bind(RATE_LIMIT_SLOT, "rate ceiling · ", "raw", false),
                // The raw expiry block-height duplicates the friendlier time-remaining bar — adept-only.
                bind(DEADLINE_SLOT,   "deadline · ", "amount", true),
            ]),
            section("Actions", "", vec![
                action("+", "Grant",    METHOD_GRANT),
                action("→", "Invoke",   METHOD_EXERCISE),
                action("⇒", "Delegate", METHOD_DELEGATE),
                action("⊘", "Revoke",   METHOD_REVOKE),
            ]),
        ]
    })
}

/// **The tool-access-delegation card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn mandate_card_json() -> String {
    serde_json::to_string(&mandate_card_value()).expect("the mandate card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn collect<'a>(node: &'a Value, kind: &str, out: &mut Vec<&'a Value>) {
        if node["kind"] == kind {
            out.push(node);
        }
        if let Some(children) = node["children"].as_array() {
            for c in children {
                collect(c, kind, out);
            }
        }
    }

    fn of_kind<'a>(card: &'a Value, kind: &str) -> Vec<&'a Value> {
        let mut out = Vec::new();
        collect(card, kind, &mut out);
        out
    }

    #[test]
    fn the_card_is_a_vstack_with_a_named_header_and_a_status_pill() {
        let card = mandate_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Tool Access Delegation"),
            "the header names the app"
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        // The header pill is LIVE: it reads CALLS_MADE_SLOT and flips to RATE-LIMITED at the ceiling.
        assert_eq!(
            pills[0]["props"]["text"], "ACTIVE",
            "the static fallback word"
        );
        assert_eq!(pills[0]["props"]["tag"], "good");
        assert_eq!(pills[0]["props"]["slot"], CALLS_MADE_SLOT);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 1, "the rate-limited edge");
        assert_eq!(cases[0]["value"], RATE_GAUGE_MAX);
        assert_eq!(cases[0]["label"], "RATE-LIMITED");
        assert_eq!(cases[0]["tag"], "warn");
    }

    #[test]
    fn the_delegation_breadcrumb_marks_the_current_step() {
        let card = mandate_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "granted → delegated → exercising → revoked");
        assert_eq!(
            items[2]["label"], "› Exercising",
            "the active step is marked"
        );
    }

    #[test]
    fn the_rate_budget_gauge_reads_the_live_calls_made_over_the_ceiling() {
        let card = mandate_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(
            gauges.len(),
            1,
            "the rate-budget gauge (calls_made / rate_limit)"
        );
        // The killer visual: the gauge fills with the LIVE meter over the granted ceiling.
        assert_eq!(gauges[0]["props"]["slot"], CALLS_MADE_SLOT);
        assert_eq!(gauges[0]["props"]["max"], RATE_GAUGE_MAX);
    }

    #[test]
    fn the_deadline_progress_shows_time_remaining() {
        let card = mandate_card_value();
        let bars = of_kind(&card, "progress");
        assert_eq!(bars.len(), 1, "the deadline time-remaining bar");
        assert_eq!(bars[0]["props"]["value"], DEADLINE_REMAINING);
        assert_eq!(bars[0]["props"]["max"], DEADLINE_WINDOW);
    }

    #[test]
    fn the_binds_surface_the_scope_meter_ceiling_and_deadline() {
        let card = mandate_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                TOOL_ID_SLOT as u64,
                CALLS_MADE_SLOT as u64,
                RATE_LIMIT_SLOT as u64,
                DEADLINE_SLOT as u64,
            ],
            "the binds surface tool / calls-used / rate-ceiling / deadline"
        );
    }

    #[test]
    fn the_mandate_binds_carry_their_display_fmt() {
        let card = mandate_card_value();
        let binds = of_kind(&card, "bind");
        let prop = |slot: u8, key: &str| -> Value {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .map(|b| b["props"][key].clone())
                .unwrap()
        };
        assert_eq!(
            prop(TOOL_ID_SLOT, "fmt"),
            "id",
            "the tool scope paints an avatar handle"
        );
        assert_eq!(
            prop(CALLS_MADE_SLOT, "fmt"),
            "raw",
            "the small call counter stays plain"
        );
        assert_eq!(
            prop(RATE_LIMIT_SLOT, "fmt"),
            "raw",
            "the small ceiling stays plain"
        );
        assert_eq!(
            prop(DEADLINE_SLOT, "fmt"),
            "amount",
            "the block height groups digits"
        );
        // The raw expiry height is adept-only (the time-remaining progress shows it friendlier).
        assert_eq!(
            prop(DEADLINE_SLOT, "adept"),
            true,
            "the raw deadline height is dev-y"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = mandate_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(
            turns,
            vec![
                METHOD_GRANT,
                METHOD_EXERCISE,
                METHOD_DELEGATE,
                METHOD_REVOKE
            ]
        );
    }

    #[test]
    fn the_actions_are_icon_labelled_rows() {
        let card = mandate_card_value();
        // One icon per action row + (no other icons), so the actions are glyph-labelled.
        let icons = of_kind(&card, "icon");
        assert_eq!(icons.len(), 4, "one glyph per lifecycle action");
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = mandate_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, breadcrumb, divider, mandate section, actions section
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
