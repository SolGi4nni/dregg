//! # identity — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree ([`deos_view::ViewNode`] in the renderer crate). The
//! SAME tree renders three ways (the renderer-independence seam): native gpui
//! pixels in the cockpit, a browser-loadable HTML document, and a discord embed —
//! all from this one piece of DATA. See `deos-view/src/{render,web,discord}.rs`
//! for the three renderers and `docs/reference/deos-view.md`.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native
//! elephants, so it is a STANDALONE workspace EXCLUDED from the repo-root
//! workspace (see its `Cargo.toml`). A starbridge-app must never depend on it —
//! that would feature-unify the elephants onto the main build. So the app's
//! contribution is the **view-tree JSON** (this module): pure `serde_json`, no
//! elephant. The deos world's renderers consume it; this module owns the card
//! definition and proves it is well-formed.
//!
//! ## The card shape — a rich, live credential-authority surface
//!
//! A titled column ([`deos.ui.vstack`](deos_view)) built from the rich deos-view
//! vocabulary (`section` / `pill` / `gauge` / `breadcrumb` / `divider` / `icon`):
//!
//!   - a **status header** — the app name + a LIVE `pill` that reads the issuance
//!     sequence ([`ISSUANCE_COUNTER_SLOT`](crate::ISSUANCE_COUNTER_SLOT)) and names
//!     the issuer's live state as a WORD (`ISSUING`; a never-issued cell reads
//!     `DORMANT`);
//!   - a **cap-tier row** of static role `pill`s naming the three parties on this
//!     credential's attenuation lattice (the ISSUER holds the signing authority; the
//!     HOLDER presents; the VERIFIER checks) — the same role legend the
//!     execution-lease / escrow cards carry;
//!   - a **lifecycle `breadcrumb`** of the credential lifecycle
//!     (issued → presented → verified → revoked) with the current step marked;
//!   - an **"Issuer authority" `section`** surfacing the LIVE cell state that makes
//!     the issuer trustworthy: a `gauge` bound to the strictly-monotonic
//!     [`ISSUANCE_COUNTER_SLOT`](crate::ISSUANCE_COUNTER_SLOT) (the issuance sequence),
//!     plus `bind`s on the issuer-key root ([`ISSUER_AUTH_ROOT_SLOT`](crate::ISSUER_AUTH_ROOT_SLOT)),
//!     the pinned schema ([`SCHEMA_COMMITMENT_SLOT`](crate::SCHEMA_COMMITMENT_SLOT)),
//!     and the raw credential-id counter (adept — the gauge already shows it);
//!   - a **"Revocation" `section`** — the append-only revocation horizon: a `gauge`
//!     on the [`REVOCATION_ROOT_SLOT`](crate::REVOCATION_ROOT_SLOT) plus a `bind` on
//!     the live status digest, so a fired `revoke` turn advances the surface;
//!   - an **"Actions" `section`** of one `icon`+`button` row per lifecycle method
//!     (`issue` / `present` / `verify` / `revoke`), each `button` carrying its
//!     `onClick = { turn, arg }` — the EXACT method symbol the
//!     [`service`](crate::service) routes through the [`invoke()`](crate::service)
//!     front door (the mutators `issue` / `revoke` desugar to verified issuer turns;
//!     the reads `present` / `verify` name the serviced seam).
//!
//! ## The honest constraint — the cell is an ISSUER, not one credential
//!
//! The backing cell is a credential ISSUER (its slots are issuance sequence,
//! revocation root, issuer-key root, schema), so the live header pill reflects
//! ISSUER ACTIVITY (`ISSUING` vs `DORMANT`), not the validity of any single
//! presented credential — there is no single-credential lifecycle slot on this
//! cell to bind. The lifecycle `breadcrumb` therefore stands as the credential
//! story; the live slot-bound nodes read what the cell genuinely holds.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary
//! ([`METHOD_ISSUE`](crate::service::METHOD_ISSUE), …) so the card and the service
//! cell speak the same lifecycle.

use serde_json::{Value, json};

use crate::service::{METHOD_ISSUE, METHOD_PRESENT, METHOD_REVOKE, METHOD_VERIFY};
use crate::{
    ISSUANCE_COUNTER_SLOT, ISSUER_AUTH_ROOT_SLOT, REVOCATION_ROOT_SLOT, SCHEMA_COMMITMENT_SLOT,
};

/// The issuance gauge's denominator — a representative issuance ceiling so a busy
/// issuer fills the bar (the `DEFAULT_ISSUER_BUDGET` is `100_000`; a smaller window
/// keeps the live sequence legible on the surface).
const ISSUANCE_GAUGE_MAX: u64 = 64;

/// The revocation gauge's denominator — a representative revocation horizon so the
/// append-only root growth reads as progress against a window.
const REVOCATION_GAUGE_MAX: u64 = 16;

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A static `deos.ui.pill` node — a colored status badge (no live slot).
fn pill(label: &str, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag } })
}

/// A LIVE `deos.ui.pill` node — reads `slot` immediate-mode and maps the value to a
/// word + color via `cases` (the first `{value,label,tag}` matching the slot wins).
/// `text`/`tag` are the static fallback (discord, or no match).
fn pill_live(slot: usize, label: &str, tag: &str, cases: Value) -> Value {
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

/// A `deos.ui.bind` node tagged with the model `slot` it re-reads + a label prefix and a
/// display `fmt` (`"id"` avatar-handle / `"hash"` short-hex / `"amount"` grouped /
/// `"raw"` plain) so an opaque key-root / commitment / counter paints short + friendly.
/// `adept` hides a dev-y row (a raw issuance counter the gauge already covers) from the
/// simple projection; revealed in the adept "see the bones" view.
fn bind(slot: usize, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

/// A `deos.ui.gauge` node — a bound progress bar (`slot_value / max`, immediate-mode).
/// `adept` hides the raw numeric in the simple projection (the friendly validity pill +
/// binds carry the meaning); revealed in the adept "see the bones" view.
fn gauge(slot: usize, max: u64, label: &str, adept: bool) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label, "adept": adept } })
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

/// An action row — an `icon` + a lifecycle `button` (the verified-turn / serviced-seam
/// affordance). The `turn` is the [`service`](crate::service) method symbol.
fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The identity card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A rich, live credential-authority surface: a status header (name + a LIVE
/// `ISSUING`/`DORMANT` pill), a cap-tier row naming the issuer / holder / verifier
/// roles, the credential-lifecycle breadcrumb, an "Issuer authority" section
/// surfacing the live issuance-sequence gauge + the issuer-key / schema / credential-id
/// binds, a "Revocation" section surfacing the append-only revocation horizon, and an
/// "Actions" section of the four icon-labelled lifecycle buttons. Renderer-independent
/// DATA: hand it to any `deos-view` renderer (native / web / discord) to paint the SAME
/// card. The button `turn` names are the [`service`](crate::service) method symbols.
pub fn identity_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            // The header pill is LIVE: it reads the issuance sequence and names the
            // issuer's state. A never-issued issuer cell (counter 0) reads DORMANT;
            // any issuer that has minted ≥1 credential falls through to ISSUING.
            row(vec![text("Identity"), pill_live(ISSUANCE_COUNTER_SLOT, "ISSUING", "good", json!([
                { "value": 0, "label": "DORMANT", "tag": "muted" },
            ]))]),
            // The three roles on this credential's attenuation lattice.
            row(vec![
                pill("issuer · authority", "accent"),
                pill("holder · presents", "muted"),
                pill("verifier · checks", "muted"),
            ]),
            breadcrumb(&["Issued", "Presented", "Verified", "Revoked"], 2),
            divider(),
            section("Issuer authority", "genuine", vec![
                gauge(ISSUANCE_COUNTER_SLOT, ISSUANCE_GAUGE_MAX, "issuance seq ", true),
                bind(ISSUER_AUTH_ROOT_SLOT, "issuer key · ", "id", false),
                bind(SCHEMA_COMMITMENT_SLOT, "schema · ", "hash", false),
                // The raw credential-id counter — the gauge already shows it.
                bind(ISSUANCE_COUNTER_SLOT, "credential id · ", "raw", true),
            ]),
            section("Revocation", "", vec![
                gauge(REVOCATION_ROOT_SLOT, REVOCATION_GAUGE_MAX, "revocation horizon ", true),
                bind(REVOCATION_ROOT_SLOT, "status · ", "hash", false),
            ]),
            section("Actions", "", vec![
                action("+", "Issue",   METHOD_ISSUE),
                action("→", "Present", METHOD_PRESENT),
                action("✓", "Verify",  METHOD_VERIFY),
                action("⊘", "Revoke",  METHOD_REVOKE),
            ]),
        ]
    })
}

/// **The identity card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses (via
/// `deos_view::parse_view_tree`). This is the string a host serves / embeds.
pub fn identity_card_json() -> String {
    serde_json::to_string(&identity_card_value()).expect("the identity card serializes")
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
    fn the_card_is_a_vstack_with_a_named_header_and_a_live_status_pill() {
        let card = identity_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts.iter().any(|t| t["props"]["text"] == "Identity"),
            "the header names the app"
        );
        // The header pill is LIVE: it reads ISSUANCE_COUNTER_SLOT and maps 0 → DORMANT.
        let live = of_kind(&card, "pill")
            .into_iter()
            .find(|p| p["props"].get("slot").is_some())
            .expect("exactly one live status pill");
        assert_eq!(live["props"]["text"], "ISSUING", "the active fallback word");
        assert_eq!(live["props"]["slot"], ISSUANCE_COUNTER_SLOT);
        let cases = live["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 1, "issuance 0 = DORMANT (never issued)");
        assert_eq!(cases[0]["value"], 0);
        assert_eq!(cases[0]["label"], "DORMANT");
    }

    #[test]
    fn the_cap_tier_row_names_the_three_credential_roles() {
        let card = identity_card_value();
        // The static (no-slot) pills name the issuer / holder / verifier roles.
        let static_pills: Vec<String> = of_kind(&card, "pill")
            .into_iter()
            .filter(|p| p["props"].get("slot").is_none())
            .map(|p| p["props"]["text"].as_str().unwrap().to_string())
            .collect();
        assert_eq!(
            static_pills,
            vec![
                "issuer · authority",
                "holder · presents",
                "verifier · checks"
            ]
        );
    }

    #[test]
    fn the_lifecycle_breadcrumb_marks_the_current_step() {
        let card = identity_card_value();
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 4, "issued → presented → verified → revoked");
        assert_eq!(items[2]["label"], "› Verified", "the active step is marked");
    }

    #[test]
    fn the_issuance_and_revocation_gauges_read_the_live_slots() {
        let card = identity_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 2, "an issuance gauge + a revocation gauge");
        assert_eq!(gauges[0]["props"]["slot"], ISSUANCE_COUNTER_SLOT);
        assert_eq!(gauges[0]["props"]["max"], ISSUANCE_GAUGE_MAX);
        assert_eq!(gauges[1]["props"]["slot"], REVOCATION_ROOT_SLOT);
        assert_eq!(gauges[1]["props"]["max"], REVOCATION_GAUGE_MAX);
    }

    #[test]
    fn the_authority_and_revocation_sections_surface_the_live_slots() {
        let card = identity_card_value();
        let titles: Vec<&str> = of_kind(&card, "section")
            .iter()
            .map(|s| s["props"]["title"].as_str().unwrap())
            .collect();
        assert_eq!(titles, vec!["Issuer authority", "Revocation", "Actions"]);
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                ISSUER_AUTH_ROOT_SLOT as u64,
                SCHEMA_COMMITMENT_SLOT as u64,
                ISSUANCE_COUNTER_SLOT as u64,
                REVOCATION_ROOT_SLOT as u64,
            ],
            "issuer key / schema / credential id (authority), then status (revocation)"
        );
    }

    #[test]
    fn the_binds_carry_their_display_fmt() {
        let card = identity_card_value();
        let binds = of_kind(&card, "bind");
        let fmt = |slot: usize| -> String {
            binds
                .iter()
                .find(|b| b["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|b| b["props"]["fmt"].as_str())
                .unwrap()
                .to_string()
        };
        // The issuer-key root paints an avatar handle; the schema / revocation-root
        // digests paint short hex; the credential id is a small sequence number (raw).
        assert_eq!(fmt(ISSUER_AUTH_ROOT_SLOT), "id");
        assert_eq!(fmt(SCHEMA_COMMITMENT_SLOT), "hash");
        assert_eq!(fmt(REVOCATION_ROOT_SLOT), "hash");
        assert_eq!(fmt(ISSUANCE_COUNTER_SLOT), "raw");
    }

    #[test]
    fn the_dev_y_rows_are_marked_adept() {
        let card = identity_card_value();
        let adept = |kind: &str, slot: usize| -> bool {
            of_kind(&card, kind)
                .iter()
                .find(|n| n["props"]["slot"].as_u64() == Some(slot as u64))
                .and_then(|n| n["props"]["adept"].as_bool())
                .unwrap()
        };
        // The raw issuance/revocation gauges + the raw credential-id counter hide in
        // the simple view; the friendly issuer key / schema / live status stay visible.
        assert!(
            adept("gauge", ISSUANCE_COUNTER_SLOT),
            "the raw issuance gauge"
        );
        assert!(
            adept("gauge", REVOCATION_ROOT_SLOT),
            "the raw revocation gauge"
        );
        assert!(
            adept("bind", ISSUANCE_COUNTER_SLOT),
            "the raw credential-id counter"
        );
        assert!(!adept("bind", ISSUER_AUTH_ROOT_SLOT));
        assert!(!adept("bind", SCHEMA_COMMITMENT_SLOT));
        assert!(
            !adept("bind", REVOCATION_ROOT_SLOT),
            "the live status stays visible"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = identity_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 4);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        // The card's button turns ARE the service method vocabulary.
        assert_eq!(
            turns,
            vec![METHOD_ISSUE, METHOD_PRESENT, METHOD_VERIFY, METHOD_REVOKE]
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = identity_card_json();
        // Round-trips through serde (the shape a deos-view renderer's parser reads).
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        // header row, cap-tier row, breadcrumb, divider, authority, revocation, actions
        assert_eq!(back["children"].as_array().unwrap().len(), 7);
    }
}
