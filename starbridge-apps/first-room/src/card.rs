//! # first-room — the composed room as a deos-view CARD (a `deos.ui.*` view-tree).
//!
//! first-room is a **composition exemplar**, not a four-axis app (see `README.md`): it
//! WELDS other apps' organs (the colonist job, the escrow economy, the room model) into
//! one runnable scenario, and owns no verified primitive of its own. So it has no
//! `FactoryDescriptor`, no service interface, no `DeosApp` — those belong to the organs it
//! composes. What it CAN ship, coherently, is the modern app's renderer-independent CARD
//! axis: a `deos.ui.*` view-tree that SHOWS the composed room — the welded organs side by
//! side, each inhabitant's held mandate, its genuine (receipted) actions, the pay, and every
//! in-room refusal with the receipt-why.
//!
//! ## Why the card is DATA, not a renderer call
//!
//! `deos-view` pulls BOTH the SpiderMonkey (`mozjs`) and the gpui native elephants, so it
//! is a STANDALONE workspace EXCLUDED from the repo-root workspace. A starbridge-app must
//! never depend on it — that would feature-unify the elephants onto the main build. So the
//! app's contribution is the **view-tree JSON** (this module): pure `serde_json`, no
//! elephant. The deos world's renderers (`render.rs`/`web.rs`/`discord.rs`) consume it; this
//! module owns the card definition and proves it is well-formed.
//!
//! ## A read-only COMPOSED VIEW — honestly STATIC, not slot-bound
//!
//! Unlike the lifecycle cards (`bounty-board`, `swarm-orchestration`), this card carries NO
//! action buttons and NO live slot-bound nodes (`bind`/`gauge`/live-`pill`). Those nodes
//! re-read a slot off ONE live backing cell each paint — but a room has no single backing
//! cell: it is the COMPOSED render of a `RoomView` snapshot the [`scenario`](crate::scenario)
//! driver produced from the real executor's receipts/refusals. So binding slots would be
//! decorative (a read against nothing). Instead the card renders the snapshot HONESTLY with
//! the rich STATIC vocabulary — `section` per inhabitant, a status `pill`, a lifecycle
//! `breadcrumb`, a `progress` of the welded chain, `icon`-tagged genuine actions / refusals,
//! a `divider`.
//!
//! ## Consumer-delight on a static card — the inline analogues of the delight props
//!
//! The live cards get their delight from slot-bound props (`bind`'s `fmt`, a live value→word
//! `pill`). A static composed view has no slot to read, so it gets the SAME delight INLINE,
//! computed from the snapshot:
//!   - an **identity** renders as a deterministic emoji-avatar handle ([`handle_for`], `🦊
//!     swift-fox`) — the static analogue of `fmt:"id"` — instead of an opaque hex prefix;
//!   - an **amount** groups its digits ([`group_digits`], `1,234,567`) — the static analogue
//!     of `fmt:"amount"`;
//!   - each inhabitant's **lifecycle** renders as a value→word status `pill` ([`status_pill`],
//!     `PAID`/`WORKING`/`PRESENT`) — the static analogue of the live value→word pill;
//!   - and **progressive disclosure** keeps the raw bones (full cell hex, receipt hashes) as
//!     `adept`-tagged nodes, so the simple projection stays clean and an adept sees the bones.
//! The actions themselves live on the organs' own service/affordance surfaces.

use serde_json::{Value, json};

use crate::room::{InhabitantView, Room, RoomView};

/// The welded lifecycle the room composes: the JOB drives `work`, the ECONOMY drives the rest.
const WELD_LIFECYCLE: [&str; 6] = ["list", "fund", "work", "ship", "settle", "paid"];

/// A `deos.ui.pill` node — a colored status badge.
fn pill(label: &str, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": label, "tag": tag } })
}

/// A `deos.ui.text` node.
fn text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s } })
}

/// A `deos.ui.text` node tagged `adept:true` — the "see the bones" detail (raw hex / hashes) the
/// `simple` disclosure projection hides and the `adept` projection reveals.
fn adept_text(s: &str) -> Value {
    json!({ "kind": "text", "props": { "text": s, "adept": true } })
}

// ── The avatar wordlists — a small local palette in the family of `deos-view`'s `fmt:"id"`
//    handle (16-emoji fauna / adjective / noun), so a static identity paints `🦊 swift-fox`
//    instead of a dev-y hex prefix. 16·16·16 = 4096 distinct friendly handles. ─────────────
const AVATAR_EMOJI: [&str; 16] = [
    "🦊", "🐢", "🦉", "🐙", "🦋", "🐝", "🐬", "🦁", "🐼", "🦅", "🦄", "🐳", "🦖", "🦜", "🦦", "🦩",
];
const AVATAR_ADJ: [&str; 16] = [
    "swift", "brave", "calm", "bright", "lucky", "noble", "quiet", "merry", "bold", "gentle",
    "clever", "sunny", "cozy", "keen", "jolly", "wise",
];
const AVATAR_NOUN: [&str; 16] = [
    "fox", "owl", "wren", "lynx", "moth", "hare", "finch", "otter", "crane", "vole", "newt", "koi",
    "dove", "elk", "mole", "swan",
];

/// A splitmix64 finalizer — decorrelates inputs so near-identical cells get visually-distinct
/// handles. Pure, wrapping.
fn mix(value: u64) -> u64 {
    let mut z = value.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// A deterministic emoji-avatar handle for a cell (`🦊 swift-fox`) — the static-card analogue of
/// a `bind`'s `fmt:"id"`: a stable, human-memorable stand-in for an opaque cell id. Same cell →
/// same handle, forever. Keyed off the cell's leading 8 bytes.
fn handle_for(cell: &dregg_app_framework::CellId) -> String {
    let b = cell.as_bytes();
    let mut seed = [0u8; 8];
    let n = b.len().min(8);
    seed[..n].copy_from_slice(&b[..n]);
    let m = mix(u64::from_be_bytes(seed));
    let e = AVATAR_EMOJI[(m & 15) as usize];
    let a = AVATAR_ADJ[((m >> 8) & 15) as usize];
    let noun = AVATAR_NOUN[((m >> 16) & 15) as usize];
    format!("{e} {a}-{noun}")
}

/// An inhabitant's lifecycle as a value→word status `pill` — the static-card analogue of the
/// live value→word pill, computed from the snapshot: `PAID` (held the reward) > `WORKING` (took
/// genuine actions) > `PRESENT` (entered, nothing yet). Tags: `good`/`accent`/`muted`.
fn status_pill(i: &InhabitantView) -> Value {
    let (word, tag) = if i.paid > 0 {
        ("PAID", "good")
    } else if !i.committed_actions.is_empty() {
        ("WORKING", "accent")
    } else {
        ("PRESENT", "muted")
    };
    pill(word, tag)
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

/// A `deos.ui.section` node — a titled, bordered container; `tag` selects the accent.
fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

/// A `deos.ui.breadcrumb` node — the welded lifecycle path; the `active` step is marked `› `.
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

/// A `deos.ui.progress` node — a STATIC (literal-valued) bar (`value / max`). The composed view is
/// a snapshot, so its progress is literal, not a live slot read.
fn progress(value: u64, max: u64, label: &str) -> Value {
    json!({ "kind": "progress", "props": { "value": value, "max": max, "label": label } })
}

/// Group a decimal's digits in threes (`1234567 → 1,234,567`) — the inline consumer-delight for an
/// amount (the static-card analogue of a `bind`'s `fmt:"amount"`, with no live slot to read).
fn group_digits(value: u64) -> String {
    let s = value.to_string();
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut out = String::with_capacity(len + len / 3);
    for (i, b) in bytes.iter().enumerate() {
        if i > 0 && (len - i) % 3 == 0 {
            out.push(',');
        }
        out.push(*b as char);
    }
    out
}

/// The full 64-char hex of a cell id (the identity "bones" — shown only in the adept projection).
fn full_hex(cell: &dregg_app_framework::CellId) -> String {
    cell.as_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

/// Render ONE inhabitant as a `deos.ui.section`: an identity row (a short-id `pill` + the name,
/// with the full cell hex as adept bones), the held mandate, the pay (a grouped amount, if any),
/// then the GENUINE (receipted) actions tagged `genuine` and the in-room REFUSALS tagged `refusal`
/// (the anti-ghost tooth made visible — the two styled distinctly, each receipt/why disclosable).
fn inhabitant_section(i: &InhabitantView) -> Value {
    // The colonist (the one that took genuine actions AND was refused) carries the section accent.
    let tag = if i.refusals.is_empty() { "" } else { "genuine" };
    // The identity paints as a friendly avatar handle (`fmt:"id"` static analogue) + the name +
    // a value→word lifecycle pill; the opaque hex prefix + full hex are adept-only bones.
    let mut children = vec![
        row(vec![
            pill(&handle_for(&i.cell), "accent"),
            text(&i.name),
            status_pill(i),
        ]),
        adept_text(&format!("cell · 0x{} ({})", full_hex(&i.cell), i.short)),
        text(&format!("mandate: {}", i.mandate)),
    ];
    if i.paid > 0 {
        children.push(row(vec![
            icon("◈", "good"),
            text(&format!(
                "holds {} CREDIT — a REAL conserving Transfer (Σδ=0)",
                group_digits(i.paid)
            )),
        ]));
    }
    for a in &i.committed_actions {
        children.push(row(vec![
            icon("✓", "genuine"),
            text(&format!("{} ", a.summary)),
        ]));
        // The receipt hash is the genuine-action's bones — disclosed only at the adept level.
        if a.receipt_hash != [0u8; 32] {
            let h: String = a.receipt_hash[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            children.push(adept_text(&format!("  receipt · 0x{h}…")));
        }
    }
    for r in &i.refusals {
        children.push(row(vec![
            icon("✗", "refusal"),
            text(&format!("{} ", r.attempted)),
        ]));
        children.push(json!({
            "kind": "text",
            "props": { "text": format!("  ⤷ {}", r.reason), "tag": "refusal" }
        }));
    }
    section(&i.name, tag, children)
}

/// **The first-room card as a `deos.ui.*` view-tree** (a `serde_json::Value`) for a rendered
/// [`RoomView`].
///
/// A `vstack`: a status header (the room name + a live/paid status `pill`), the welded-lifecycle
/// `breadcrumb` (`list → fund → work → ship → settle → paid`), a "The weld" `section` that names
/// the two organs and how the JOB gates the conserving pay, then one nested `section` per
/// inhabitant (identity, mandate, pay, genuine actions, in-room refusals). Renderer-independent
/// DATA: hand it to any `deos-view` renderer (native / web / discord) to paint the SAME composed
/// room — and at the `simple` disclosure level the raw hex / receipt bones stay hidden.
pub fn room_card_value(room: &RoomView) -> Value {
    // Snapshot facts, read from the composed room (no live slot — the view is a render).
    let paid_total: u64 = room.inhabitants.iter().map(|i| i.paid).sum();
    let job_steps: u64 = room
        .inhabitants
        .iter()
        .map(|i| i.committed_actions.len() as u64)
        .sum::<u64>();
    let refusals: u64 = room
        .inhabitants
        .iter()
        .map(|i| i.refusals.len() as u64)
        .sum();
    let (status, status_tag) = if paid_total > 0 {
        ("PAID", "good")
    } else {
        ("LIVE", "accent")
    };
    // The welded chain reaches `paid` once the colonist holds the reward; else it is still at `work`.
    let active = if paid_total > 0 { 5 } else { 2 };
    let stages_done = (active + 1) as u64;

    let weld = section(
        "The weld",
        "genuine",
        vec![
            text("JOB (gather → make → hand-off) ↔ ECONOMY (escrow list → fund → ship → settle)"),
            text(
                "on completion the JOB gates a REAL conserving Transfer of the reward (the shared Payable interface) — the colonist HOLDS it.",
            ),
            progress(stages_done, WELD_LIFECYCLE.len() as u64, "lifecycle "),
            row(vec![
                pill(&format!("{job_steps} genuine"), "genuine"),
                pill(&format!("{refusals} refused"), "refusal"),
            ]),
        ],
    );

    let mut children = vec![
        row(vec![
            text(&format!("First Room — {}", room.name)),
            pill(status, status_tag),
        ]),
        breadcrumb(&WELD_LIFECYCLE, active),
        divider(),
        weld,
    ];
    for i in &room.inhabitants {
        children.push(inhabitant_section(i));
    }
    json!({ "kind": "vstack", "props": {}, "children": children })
}

/// **The first-room card as a `deos.ui.*` view-tree for a live [`Room`]** — the convenience over
/// [`room_card_value`] that renders the room first.
pub fn card_for_room(room: &Room) -> Value {
    room_card_value(&room.render())
}

/// **The first-room card as serialized `deos.ui.*` JSON** — byte-for-byte the
/// `JSON.stringify(tree)` shape a `deos-view` renderer parses. This is the string a host
/// serves / embeds.
pub fn room_card_json(room: &RoomView) -> String {
    serde_json::to_string(&room_card_value(room)).expect("the first-room card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::room::{GenuineAction, InRoomRefusal, InhabitantView, Room};
    use crate::run_first_room;
    use dregg_app_framework::CellId;

    /// Walk the tree collecting every node of `kind`.
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

    fn demo_room() -> Room {
        let mut room = Room::new(CellId::from_bytes([1u8; 32]), "the workshop");
        room.enter(InhabitantView {
            cell: CellId::from_bytes([2u8; 32]),
            short: "0202…".into(),
            name: "the colonist".into(),
            mandate: "JOB: gather→make→hand-off".into(),
            committed_actions: vec![GenuineAction {
                summary: "Gather (step 0→1)".into(),
                receipt_hash: [7u8; 32],
            }],
            refusals: vec![InRoomRefusal {
                attempted: "skip a prerequisite step".into(),
                reason: "refused by MonotonicSequence(JOB_CURSOR) — program".into(),
            }],
            paid: 800,
        });
        room
    }

    #[test]
    fn the_card_is_a_vstack_with_a_status_header_and_a_section_per_inhabitant() {
        let room = demo_room();
        let card = card_for_room(&room);
        assert_eq!(card["kind"], "vstack");
        // header row, breadcrumb, divider, weld section, + one inhabitant section.
        let children = card["children"].as_array().expect("children");
        assert_eq!(children.len(), 5);
        // The header row names the room and carries the status pill.
        let header = &children[0];
        assert_eq!(header["kind"], "row");
        let texts = of_kind(header, "text");
        assert_eq!(texts[0]["props"]["text"], "First Room — the workshop");
        let header_pills = of_kind(header, "pill");
        assert_eq!(
            header_pills[0]["props"]["text"], "PAID",
            "paid → PAID status"
        );
        // The last child is the inhabitant section.
        assert_eq!(children[4]["kind"], "section");
        assert_eq!(children[4]["props"]["title"], "the colonist");
    }

    #[test]
    fn the_welded_lifecycle_breadcrumb_marks_the_reached_step() {
        let card = card_for_room(&demo_room());
        let crumbs = of_kind(&card, "breadcrumb");
        assert_eq!(crumbs.len(), 1);
        let items = crumbs[0]["props"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 6, "list → fund → work → ship → settle → paid");
        assert_eq!(items[5]["label"], "› paid", "a paid room reached the end");
    }

    #[test]
    fn the_inhabitant_section_tags_genuine_actions_and_refusals_distinctly() {
        let card = card_for_room(&demo_room());
        let section = card["children"].as_array().unwrap().last().unwrap();
        let icons = of_kind(section, "icon");
        let genuine = icons.iter().find(|n| n["props"]["tag"] == "genuine");
        assert!(
            genuine.is_some(),
            "a genuine action carries a ✓ genuine icon"
        );
        let refusal = icons.iter().find(|n| n["props"]["tag"] == "refusal");
        assert!(refusal.is_some(), "a refusal carries a ✗ refusal icon");
        // The refusal carries its receipt-why with the tooth.
        let refusal_text = of_kind(section, "text")
            .into_iter()
            .find(|n| n["props"]["tag"] == "refusal")
            .unwrap();
        assert!(
            refusal_text["props"]["text"]
                .as_str()
                .unwrap()
                .contains("refused by")
        );
    }

    #[test]
    fn the_pay_is_a_grouped_amount_and_the_bones_are_adept_only() {
        let card = card_for_room(&demo_room());
        // The pay renders as a grouped, conserving-Transfer line.
        let paid = of_kind(&card, "text")
            .into_iter()
            .find(|n| {
                n["props"]["text"]
                    .as_str()
                    .map(|s| s.contains("holds") && s.contains("CREDIT"))
                    .unwrap_or(false)
            })
            .expect("the pay line");
        assert!(paid["props"]["text"].as_str().unwrap().contains("Σδ=0"));
        // The raw cell hex + the receipt hash lift as adept-only bones (hidden in the simple view).
        let adept: Vec<&Value> = of_kind(&card, "text")
            .into_iter()
            .filter(|n| n["props"]["adept"] == true)
            .collect();
        assert!(
            adept.iter().any(|n| n["props"]["text"]
                .as_str()
                .unwrap()
                .starts_with("cell · 0x")),
            "the full cell hex is adept-only"
        );
        assert!(
            adept.iter().any(|n| n["props"]["text"]
                .as_str()
                .unwrap()
                .contains("receipt · 0x")),
            "the receipt hash is adept-only"
        );
    }

    #[test]
    fn the_inhabitant_identity_paints_an_avatar_handle_and_a_status_pill() {
        let card = card_for_room(&demo_room());
        let section = card["children"].as_array().unwrap().last().unwrap();
        let pills = of_kind(section, "pill");
        // The identity paints a friendly emoji-avatar handle (the `fmt:"id"` static analogue) —
        // `🦊 swift-fox`, an `adj-noun` form — not the opaque `0202…` hex prefix (now adept-only).
        assert!(
            pills.iter().any(|p| {
                let t = p["props"]["text"].as_str().unwrap();
                t.contains(' ') && t.contains('-') && !t.contains('…')
            }),
            "the identity paints a friendly avatar handle, not a hex prefix"
        );
        assert!(
            of_kind(section, "text")
                .iter()
                .all(|t| !t["props"]["text"].as_str().unwrap().starts_with("0")),
            "the bare hex prefix is no longer in the simple identity row"
        );
        // The colonist holds the reward → a PAID/good lifecycle pill (the value→word analogue).
        assert!(
            pills
                .iter()
                .any(|p| p["props"]["text"] == "PAID" && p["props"]["tag"] == "good"),
            "the paid colonist shows a PAID status pill"
        );
    }

    #[test]
    fn the_status_pill_maps_each_lifecycle_to_a_word() {
        let base = InhabitantView {
            cell: CellId::from_bytes([3u8; 32]),
            short: "0303…".into(),
            name: "x".into(),
            mandate: "m".into(),
            committed_actions: vec![],
            refusals: vec![],
            paid: 0,
        };
        assert_eq!(status_pill(&base)["props"]["text"], "PRESENT");
        let working = InhabitantView {
            committed_actions: vec![GenuineAction {
                summary: "s".into(),
                receipt_hash: [0u8; 32],
            }],
            ..base.clone()
        };
        assert_eq!(status_pill(&working)["props"]["text"], "WORKING");
        let paid = InhabitantView { paid: 5, ..base };
        assert_eq!(status_pill(&paid)["props"]["text"], "PAID");
    }

    #[test]
    fn the_avatar_handle_is_deterministic_per_cell() {
        let c = CellId::from_bytes([7u8; 32]);
        assert_eq!(handle_for(&c), handle_for(&c), "same cell → same handle");
        let d = CellId::from_bytes([8u8; 32]);
        assert_ne!(
            handle_for(&c),
            handle_for(&d),
            "distinct cells → distinct handles (here)"
        );
    }

    #[test]
    fn the_card_serializes_to_parseable_json() {
        let s = room_card_json(&demo_room().render());
        let back: Value = serde_json::from_str(&s).expect("the card JSON parses");
        assert_eq!(back["kind"], "vstack");
    }

    #[test]
    fn the_card_renders_the_real_welded_scenario_room() {
        // The card renders the ACTUAL room the scenario produces from the real executor — the
        // colonist + the payer, the genuine job steps, the REAL conserved pay, and all five in-room
        // refusals from the try-to-cheat battery.
        let t = run_first_room();
        let card = card_for_room(&t.room);
        let children = card["children"].as_array().unwrap();
        // header + breadcrumb + divider + weld + one section per inhabitant.
        assert_eq!(children.len(), 4 + t.room.occupancy());
        // Every cheat is rendered in-room as a tagged refusal (the anti-ghost surface).
        let refusal_icons = of_kind(&card, "icon")
            .into_iter()
            .filter(|n| n["props"]["tag"] == "refusal")
            .count();
        assert_eq!(refusal_icons, 5, "the five cheat refusals render in-room");
        // The weld section names the composition and shows the lifecycle progress.
        let progress = of_kind(&card, "progress");
        assert_eq!(progress.len(), 1, "the welded-lifecycle progress");
        assert_eq!(progress[0]["props"]["max"], 6);
    }
}
