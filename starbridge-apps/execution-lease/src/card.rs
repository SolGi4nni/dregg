//! # execution-lease — the UI as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! The fourth axis of a modern starbridge-app: the app lives IN the deos world by
//! shipping its surface as a **renderer-independent card** — a serializable
//! `deos.ui.*` element-tree. The SAME tree renders three ways (native gpui in the
//! cockpit, a browser HTML document, a discord embed), all from this one piece of
//! DATA. The app's contribution is the view-tree JSON (pure `serde_json`, no
//! renderer dependency): the deos world's renderers consume it.
//!
//! ## The card shape — a live durable-execution-lease dashboard
//!
//! A titled column built from the rich deos-view vocabulary:
//!
//!   * a **status header** — the app name + a LIVE `pill` reading
//!     [`LAPSED_SLOT`](crate::LAPSED_SLOT) and naming the lease state
//!     (`LIVE` / `LAPSED`), and a `breadcrumb` of the lease lifecycle
//!     (Open → Running → Lapsed) with the current band marked;
//!   * a **"Lease" `section`** surfacing the LIVE cell state: the KILLER VISUAL is a
//!     `gauge` bound to [`PERIODS_PAID_SLOT`](crate::PERIODS_PAID_SLOT) over a demo
//!     lease length (the rent paid as periods elapse) plus `bind`s on the durable
//!     checkpoint [`STEP_SLOT`](crate::STEP_SLOT), the
//!     [`STATE_DIGEST_SLOT`](crate::STATE_DIGEST_SLOT), the
//!     [`RENT_SLOT`](crate::RENT_SLOT) and the [`PROVIDER_SLOT`](crate::PROVIDER_SLOT);
//!   * an **"Actions" `section`** of one `icon`+`button` row per service operation
//!     (`pay` / `advance` / `status`), each `button` carrying its `onClick`.
//!
//! The button `turn` names match the [`service`](crate::service) method vocabulary.

use serde_json::{Value, json};

use crate::service::{METHOD_ADVANCE, METHOD_PAY, METHOD_STATUS};
use crate::{
    LAPSED_SLOT, PERIODS_PAID_SLOT, PROVIDER_SLOT, RENT_SLOT, STATE_DIGEST_SLOT, STEP_SLOT,
};

/// The demo lease length the periods-paid gauge fills over.
pub const DEMO_LEASE_PERIODS: u64 = 12;

fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

fn pill_live(slot: usize, label: &str, tag: &str, cases: Value) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag, "slot": slot, "cases": cases } })
}

fn icon(glyph: &str, tag: &str) -> Value {
    json!({ "kind": "icon", "props": { "glyph": glyph, "tag": tag } })
}

fn divider() -> Value {
    json!({ "kind": "divider", "props": {} })
}

fn row(children: Vec<Value>) -> Value {
    json!({ "kind": "row", "props": {}, "children": children })
}

fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

fn bind(slot: usize, label: &str, fmt: &str, adept: bool) -> Value {
    json!({ "kind": "bind", "props": { "slot": slot, "label": label, "fmt": fmt, "adept": adept } })
}

fn gauge(slot: usize, max: u64, label: &str) -> Value {
    json!({ "kind": "gauge", "props": { "slot": slot, "max": max, "label": label } })
}

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

fn button(label: &str, turn: &str, arg: i64) -> Value {
    json!({
        "kind": "button",
        "props": { "label": label, "onClick": { "turn": turn, "arg": arg } }
    })
}

fn action(glyph: &str, label: &str, turn: &str) -> Value {
    row(vec![icon(glyph, "accent"), button(label, turn, 0)])
}

/// **The execution-lease card as a `deos.ui.*` view-tree** (a `serde_json::Value`).
///
/// A live durable-execution-lease dashboard: a status header (name + LIVE/LAPSED
/// pill + lease-lifecycle breadcrumb), a "Lease" section whose KILLER VISUAL is the
/// periods-paid gauge (rent paid as periods elapse) plus the durable-checkpoint
/// step / state-digest / rent / provider binds, and an "Actions" section of the
/// pay / advance / status buttons. Renderer-independent DATA. The button `turn`
/// names are the [`service`](crate::service) method symbols.
pub fn lease_card_value() -> Value {
    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            // The header pill reads the LIVE lapsed slot and names the lease state.
            row(vec![text("Durable Execution Lease"), pill_live(LAPSED_SLOT as usize, "LIVE", "good", json!([
                { "value": 0, "label": "LIVE",   "tag": "good" },
                { "value": 1, "label": "LAPSED", "tag": "danger" },
            ]))]),
            breadcrumb(&["Open", "Running", "Lapsed"], 1),
            divider(),
            section("Lease", "genuine", vec![
                // THE KILLER VISUAL: the rent paid as periods elapse.
                gauge(PERIODS_PAID_SLOT as usize, DEMO_LEASE_PERIODS, "periods paid "),
                // The durable checkpoint cursor (the umem heap image step).
                bind(STEP_SLOT as usize, "checkpoint · ", "amount", false),
                bind(STATE_DIGEST_SLOT as usize, "state digest · ", "hash", false),
                bind(RENT_SLOT as usize, "rent/period · ", "amount", false),
                bind(PROVIDER_SLOT as usize, "provider · ", "id", false),
            ]),
            section("Actions", "", vec![
                action("$", "Pay rent",   METHOD_PAY),
                action("→", "Advance",    METHOD_ADVANCE),
                action("≡", "Status",     METHOD_STATUS),
            ]),
        ]
    })
}

/// **The execution-lease card as serialized `deos.ui.*` JSON** — the string a host
/// serves / embeds (`JSON.stringify(tree)` shape a `deos-view` renderer parses).
pub fn lease_card_json() -> String {
    serde_json::to_string(&lease_card_value()).expect("the lease card serializes")
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
        let card = lease_card_value();
        assert_eq!(card["kind"], "vstack");
        let texts = of_kind(&card, "text");
        assert!(
            texts
                .iter()
                .any(|t| t["props"]["text"] == "Durable Execution Lease")
        );
        let pills = of_kind(&card, "pill");
        assert_eq!(pills.len(), 1);
        assert_eq!(pills[0]["props"]["slot"], LAPSED_SLOT as usize);
        let cases = pills[0]["props"]["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 2, "LIVE / LAPSED");
        assert_eq!(cases[1]["label"], "LAPSED");
    }

    #[test]
    fn the_periods_gauge_reads_the_live_periods_paid_slot() {
        let card = lease_card_value();
        let gauges = of_kind(&card, "gauge");
        assert_eq!(gauges.len(), 1, "the killer visual: the periods-paid gauge");
        assert_eq!(gauges[0]["props"]["slot"], PERIODS_PAID_SLOT as usize);
        assert_eq!(gauges[0]["props"]["max"], DEMO_LEASE_PERIODS);
    }

    #[test]
    fn the_lease_binds_surface_the_durable_cursor() {
        let card = lease_card_value();
        let binds = of_kind(&card, "bind");
        let slots: Vec<u64> = binds
            .iter()
            .map(|b| b["props"]["slot"].as_u64().unwrap())
            .collect();
        assert_eq!(
            slots,
            vec![
                STEP_SLOT as u64,
                STATE_DIGEST_SLOT as u64,
                RENT_SLOT as u64,
                PROVIDER_SLOT as u64
            ],
            "the binds surface checkpoint / digest / rent / provider"
        );
    }

    #[test]
    fn every_button_carries_its_service_method_as_the_turn_payload() {
        let card = lease_card_value();
        let buttons = of_kind(&card, "button");
        assert_eq!(buttons.len(), 3);
        let turns: Vec<&str> = buttons
            .iter()
            .map(|b| b["props"]["onClick"]["turn"].as_str().unwrap())
            .collect();
        assert_eq!(turns, vec![METHOD_PAY, METHOD_ADVANCE, METHOD_STATUS]);
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = lease_card_json();
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
        assert_eq!(back["children"].as_array().unwrap().len(), 5);
    }
}
