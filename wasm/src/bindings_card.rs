//! The **card-in-the-tab** drive loop — the wasm analog of the native
//! [`deos_js::applet::Applet::fire`].
//!
//! A deos-js card renders renderer-independently: the SAME `ViewNode` tree paints to
//! gpui pixels natively (`deos-view`'s `render`) AND to browser HTML (`deos-view`'s
//! `web` renderer). The web renderer carries each `button`'s `{turn, arg}` affordance
//! into the DOM (`data-turn`/`data-arg`) and dispatches a `deos-affordance` CustomEvent
//! on click — but the LIVE turn was the named seam: a browser click had no cap-gated
//! verified executor to fire into.
//!
//! This module CLOSES that seam **in the tab**. `mozjs` (the native `deos-js` engine)
//! can't link on wasm32, so we don't carry `Applet` here — but its `fire` loop is
//! tiny and rests entirely on the embedded `DreggEngine` (via [`crate::runtime`]),
//! which IS in the wasm graph. So we re-express the SAME loop with the SAME effects:
//!
//! `Applet::fire("inc", 1)` natively builds an action of `Effect::SetField { slot,
//! count+arg }` + `Effect::IncrementNonce`, runs it through the embedded verified
//! executor, and re-reads the bound slot. [`CardWorld::fire`] here does precisely
//! that — a REAL signed turn through the canonical [`crate::runtime::DreggRuntime`]
//! executor (the same `execute_turn_for_agent` every other wasm turn rides), leaving
//! a real receipt. The browser's `deos-affordance` listener calls [`CardWorld::fire`]
//! and re-paints the `data-slot` bind from the returned value — the SolidJS-shaped
//! signal re-render, but every "+1" is now a cap-gated verified turn, not a console
//! log.
//!
//! The `u64`↔felt packing mirrors `deos_js::applet::{pack_u64, unpack_u64}`
//! (little-endian into the first 8 bytes of the 32-byte field element), so the value
//! a card binds in the tab is byte-identical to the value the native applet binds.

use wasm_bindgen::prelude::*;

use dregg_turn::{Effect, TurnResult};

use crate::runtime::DreggRuntime;

use deos_reflect::substance::FieldValue;
use deos_reflect::{AffordanceSurface, ReflectedCell};
use dregg_cell::AuthRequired;

/// Pack a `u64` into a 32-byte field element — little-endian into the low 8 bytes.
/// Byte-identical to `deos_js::applet::pack_u64` (the native applet's slot encoding).
fn pack_u64(v: u64) -> [u8; 32] {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

/// Read a `u64` back out of a field element's low 8 bytes. Mirrors
/// `deos_js::applet::unpack_u64`.
fn unpack_u64(fe: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

/// A single deos-js card, driven from the browser tab over its own embedded verified
/// executor. One `CardWorld` owns one runtime with one card-cell (agent 0); its
/// affordances are fired as REAL cap-gated verified turns — the wasm realization of
/// the native [`deos_js::applet::Applet`].
#[wasm_bindgen]
pub struct CardWorld {
    rt: DreggRuntime,
    /// The model slot the card binds (the counter card binds slot 0).
    slot: usize,
}

#[wasm_bindgen]
impl CardWorld {
    /// Mint a fresh card on its own embedded executor, seeding model `slot` to
    /// `initial`. The card-cell is agent 0 (genesis) — single-custody, the same
    /// posture `Applet::mint` gives the native applet (`AuthRequired::None` holder,
    /// open permissions on its own cell).
    ///
    /// `slot` is which model field the card's `bind` reads (the counter card's
    /// `{ "kind": "bind", "slot": 0 }`).
    #[wasm_bindgen(constructor)]
    pub fn new(slot: usize, initial: u64) -> Result<CardWorld, JsError> {
        let mut rt = DreggRuntime::new();
        // Genesis card-cell: the agent of every turn, with a fee balance so a metered
        // turn has a source (mirrors `Applet::mint`'s 1M-computron seed).
        rt.try_create_agent("card", 1_000_000)
            .map_err(|e| JsError::new(&e))?;
        let mut world = CardWorld { rt, slot };
        if initial != 0 {
            // Seed the genesis model value via a real verified turn (no out-of-band
            // poke into the ledger): the same SetField + IncrementNonce shape a fire
            // uses, so the seed itself leaves a receipt.
            world.commit_set(initial).map_err(|e| JsError::new(&e))?;
        }
        Ok(world)
    }

    /// The card-cell's id (hex) — the sovereignty boundary, the agent of its turns.
    #[wasm_bindgen(js_name = cellId)]
    pub fn cell_id(&self) -> String {
        crate::bindings::hex_encode(&self.rt.agents[0].cell_id.0)
    }

    /// A witnessed read of the bound slot off the live ledger — the SAME read the
    /// card's `bind` makes (`Applet::get_u64`). The value the web renderer paints
    /// into the `data-slot` span.
    pub fn read(&self) -> u64 {
        let cell_id = self.rt.agents[0].cell_id;
        self.rt
            .cell_field(&cell_id, self.slot)
            .map(|fe| unpack_u64(&fe))
            .unwrap_or(0)
    }

    /// **Fire a card affordance** — commit ONE cap-gated verified turn, then return the
    /// re-read bound value (the new `bind` value the browser re-paints).
    ///
    /// This is `Applet::fire` in the tab. `turn` is the affordance name the web
    /// renderer carried as `data-turn`; `arg` is `data-arg`. The counter card's `"inc"`
    /// affordance computes its write as a pure function of the live model
    /// (`count := count + arg`) and commits it through the canonical executor. An
    /// unknown affordance commits nothing and errors (the native `FireError::Unknown`).
    ///
    /// `arg` is an `i32` so wasm-bindgen maps it to a plain JS `number` — the affordance
    /// wire calls `card.fire("inc", parseInt(data-arg))`, NOT `card.fire("inc", 1n)`. (An
    /// `i64` would map to a `BigInt` and the wire's plain number would throw "Cannot
    /// convert N to a BigInt".) It is widened to the canonical `i64` the native
    /// `Applet::fire` carries before being applied to the model.
    pub fn fire(&mut self, turn: &str, arg: i32) -> Result<u64, JsError> {
        let arg = arg as i64;
        match turn {
            "inc" => {
                // writes = pure function of the live model — exactly the counter
                // card's `apply` closure (`deos.ui` counter: count := count + arg).
                let current = self.read();
                let next = (current as i64).saturating_add(arg).max(0) as u64;
                self.commit_set(next)
                    .map_err(|e| JsError::new(&e.to_string()))?;
                Ok(self.read())
            }
            other => Err(JsError::new(&format!("unknown affordance: {other}"))),
        }
    }

    /// The committed-receipt count — the audit tape length (one per fired turn). A
    /// browser can show it to prove the fire was a real turn, not a local mutation.
    #[wasm_bindgen(js_name = receiptCount)]
    pub fn receipt_count(&self) -> usize {
        self.rt.receipts.len()
    }

    /// Commit the bound slot to `value` as a REAL verified turn: `Effect::SetField`
    /// on the card-cell's own slot + `Effect::IncrementNonce` (so the next turn
    /// chains and the model witnesses the write) — the SAME two effects
    /// `Applet::fire` builds. Routed through `execute_turn_for_agent` (signs the
    /// call-forest with the card's cipherclerk, runs the canonical executor, leaves
    /// a receipt). A rejected turn is surfaced, never silently swallowed.
    fn commit_set(&mut self, value: u64) -> Result<(), String> {
        let cell_id = self.rt.agents[0].cell_id;
        let effects = vec![
            Effect::SetField {
                cell: cell_id,
                index: self.slot,
                value: pack_u64(value),
            },
            Effect::IncrementNonce { cell: cell_id },
        ];
        match self.rt.execute_turn_for_agent(0, effects, 10_000) {
            TurnResult::Committed { .. } => Ok(()),
            TurnResult::Rejected { reason, at_action } => {
                Err(format!("turn rejected: {reason} (at {at_action:?})"))
            }
            other => Err(format!("turn not committed: {other:?}")),
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════
//  THE REFLECTIVE-INSPECTOR CARD, IN THE TAB
// ════════════════════════════════════════════════════════════════════════════════════════
//
// `CardWorld` above carries the *counter* card (one bound slot, one `inc` affordance). This
// carries the **reflective-inspector card** — the cockpit's inspector surface
// (`deos_js::inspector_card`), reborn as a deos-js card, but driven from a browser TAB over
// its own embedded verified executor.
//
// The native inspector card (`deos_js::inspector_card::inspector_view_for`) generates a
// view-tree from a focused cell's MOLDABLE REFLECTIVE FACES: a "Cell State" section (a live
// `Bind` row per revealed scalar slot + a labeled `Text` per structural substance — balance,
// nonce, caps, lifecycle, …) and an "Affordances" section (a cap-gated `Button` per fireable
// affordance). `mozjs` can't link on wasm32 so we don't carry the deos-js `Applet` here — but
// that generator rests entirely on `deos-reflect` (`ReflectedCell::raw_fields` +
// `AffordanceSurface::project_for`), which IS in the wasm graph. So [`InspectorWorld`]
// re-expresses the SAME generator over its own in-tab cell (`inspector_view_tree_json`,
// below) and exposes the SAME firing loop: an affordance `Button`'s click fires a REAL
// cap-gated verified turn over the embedded executor and the bound field rows re-paint from
// the committed ledger. This is the inspector — a fully-reflective cockpit surface — running
// in a browser, not just the native cockpit.

/// The model slots the inspector card's focused cell carries as live fields. They are low
/// USER slots (disjoint from the kernel-reserved `fields[3]`/`fields[4]` escrow/queue roots,
/// and from slot 14 the native inspector bumps for authorship provenance), so they surface as
/// `Revealed` `FieldSlot`s in the RawFields face — i.e. as live `Bind` rows the renderer
/// re-reads off the ledger. Seeding them non-zero is what makes them appear (the reflective
/// read only surfaces non-trivial slots, to keep the view legible).
const INSPECTOR_FIELD_SLOTS: [usize; 3] = [0, 1, 2];

/// The reflective-inspector card, driven from the browser tab over its own embedded verified
/// executor. One `InspectorWorld` owns one runtime with one focused card-cell (agent 0); its
/// view-tree is generated from that cell's REAL faces ([`Self::view_tree_json`]) and its
/// affordances fire as REAL cap-gated verified turns — the wasm realization of the native
/// [`deos_js::inspector_card`] over a live World.
#[wasm_bindgen]
pub struct InspectorWorld {
    rt: DreggRuntime,
}

#[wasm_bindgen]
impl InspectorWorld {
    /// Mint a fresh inspector card on its own embedded executor, focused on a genesis
    /// card-cell with a few seeded scalar state slots (so the RawFields face shows live
    /// `Bind` rows). The cell is agent 0 (single-custody, `AuthRequired::None` holder — the
    /// posture `Applet::mint` gives a card), funded so a metered turn has a source.
    ///
    /// `seeds[i]` seeds [`INSPECTOR_FIELD_SLOTS`]`[i]` (clamped to the available slots); each
    /// seed is committed via a REAL verified turn (no out-of-band poke), so the genesis state
    /// itself leaves receipts. Pass an empty/short array to seed the defaults.
    #[wasm_bindgen(constructor)]
    pub fn new(seeds: Vec<u64>) -> Result<InspectorWorld, JsError> {
        let mut rt = DreggRuntime::new();
        rt.try_create_agent("inspector", 1_000_000)
            .map_err(|e| JsError::new(&e))?;
        let mut world = InspectorWorld { rt };
        // Default seeds give a legible, clearly-distinct three-field cell.
        let defaults = [7u64, 42u64, 100u64];
        for (i, &slot) in INSPECTOR_FIELD_SLOTS.iter().enumerate() {
            let value = seeds.get(i).copied().unwrap_or(defaults[i]);
            if value != 0 {
                world
                    .commit_set(slot, value)
                    .map_err(|e| JsError::new(&e))?;
            }
        }
        Ok(world)
    }

    /// The focused card-cell's id (hex) — the sovereignty boundary, the agent of its turns.
    #[wasm_bindgen(js_name = cellId)]
    pub fn cell_id(&self) -> String {
        crate::bindings::hex_encode(&self.rt.agents[0].cell_id.0)
    }

    /// A witnessed read of model `slot` off the live ledger — the SAME read the inspector's
    /// `Bind` row makes (`Applet::get_u64`). The value the web renderer paints into the
    /// matching `data-slot` span. (Takes a `slot` arg — the inspector binds SEVERAL slots,
    /// unlike the single-slot counter `CardWorld::read`.)
    pub fn read(&self, slot: usize) -> u64 {
        let cell_id = self.rt.agents[0].cell_id;
        self.rt
            .cell_field(&cell_id, slot)
            .map(|fe| unpack_u64(&fe))
            .unwrap_or(0)
    }

    /// The focused cell's balance (a structural substance the RawFields face shows) — a
    /// witnessed read for the live status strip.
    pub fn balance(&self) -> i64 {
        let cell_id = self.rt.agents[0].cell_id;
        self.rt
            .ledger
            .get(&cell_id)
            .map(|c| c.state.balance())
            .unwrap_or(0)
    }

    /// The focused cell's nonce (the turn counter — another structural substance). Advances by
    /// one per fired affordance (each turn carries an `IncrementNonce`).
    pub fn nonce(&self) -> u64 {
        let cell_id = self.rt.agents[0].cell_id;
        self.rt
            .ledger
            .get(&cell_id)
            .map(|c| c.state.nonce())
            .unwrap_or(0)
    }

    /// The committed-receipt count — the audit tape length (one per fired turn, plus the
    /// genesis seeds). A browser shows it to prove a fire was a real turn, not a local poke.
    #[wasm_bindgen(js_name = receiptCount)]
    pub fn receipt_count(&self) -> usize {
        self.rt.receipts.len()
    }

    /// **THE INSPECTOR VIEW-TREE, GENERATED FROM THE LIVE CELL'S FACES.** Reads the focused
    /// cell's RawFields + Affordances faces off the live ledger (via [`deos_reflect`], the
    /// SAME substrate the native `inspector_view_for` reads) and lifts them into the view-tree
    /// JSON the web renderer (`deos-view`) parses: a titled column with a "Cell State" section
    /// (a `Bind` row per revealed scalar slot, a `Text` per structural substance) and an
    /// "Affordances" section (a `Button` per affordance the holder may fire). This is the
    /// inspector card's `view_source` — serve it to the renderer and the focused cell's faces
    /// paint live in a browser. Regenerate after a fire and a newly-non-zero slot appears as a
    /// fresh `Bind` row (the reflective view tracks the live state).
    #[wasm_bindgen(js_name = viewTreeJson)]
    pub fn view_tree_json(&self) -> String {
        let cell_id = self.rt.agents[0].cell_id;
        inspector_view_tree_json(&self.rt, cell_id, &self.held(), &self.affordance_specs())
    }

    /// **Fire one of the focused cell's affordances** — commit ONE cap-gated verified turn on
    /// the live World (exactly what a rendered affordance `Button`'s click does), then return
    /// the re-read value of the slot it advanced (the new `Bind` value the browser re-paints).
    ///
    /// `turn` is the affordance name the web renderer carried as `data-turn`; `arg` is
    /// `data-arg`. The inspector card's affordances each advance one bound slot as a pure
    /// function of the live model (so the bound row updates in place) and commit it through the
    /// canonical executor, leaving a real receipt. An unknown affordance commits nothing and
    /// errors (the native `FireError::Unknown`).
    ///
    /// `arg` is an `i32` (maps to a plain JS `number`, not a `BigInt`) — the affordance wire
    /// calls `card.fire("tick", parseInt(data-arg))`. Widened to the canonical `i64` before it
    /// touches the model.
    pub fn fire(&mut self, turn: &str, arg: i32) -> Result<u64, JsError> {
        let arg = arg as i64;
        let slot = affordance_slot(turn)
            .ok_or_else(|| JsError::new(&format!("unknown affordance: {turn}")))?;
        let current = self.read(slot);
        let next = (current as i64).saturating_add(arg).max(0) as u64;
        self.commit_set(slot, next).map_err(|e| JsError::new(&e))?;
        Ok(self.read(slot))
    }

    // ── internals ───────────────────────────────────────────────────────────────────────

    /// The authority the inspector card's driver holds. `AuthRequired::None` (single-custody,
    /// the card's own cell) — the same posture `Applet::mint` gives a card; the affordances are
    /// projected (cap-gated) against it, and the EXECUTOR enforces the real guarantee on fire.
    fn held(&self) -> AuthRequired {
        AuthRequired::None
    }

    /// The affordance set the inspector card publishes — one per writable bound slot, each a
    /// real `SetField` effect on that slot (the `effect_template` `deos-reflect` cap-gates).
    /// Their names are the `data-turn` payloads the rendered buttons fire.
    fn affordance_specs(&self) -> Vec<(String, AuthRequired)> {
        AFFORDANCES
            .iter()
            .map(|(name, _)| (name.to_string(), AuthRequired::None))
            .collect()
    }

    /// Commit `slot := value` on the focused cell as a REAL verified turn (`SetField` +
    /// `IncrementNonce` — the SAME two effects `Applet::fire` builds), routed through
    /// `execute_turn_for_agent`. A rejected turn is surfaced, never swallowed.
    fn commit_set(&mut self, slot: usize, value: u64) -> Result<(), String> {
        let cell_id = self.rt.agents[0].cell_id;
        let effects = vec![
            Effect::SetField {
                cell: cell_id,
                index: slot,
                value: pack_u64(value),
            },
            Effect::IncrementNonce { cell: cell_id },
        ];
        match self.rt.execute_turn_for_agent(0, effects, 10_000) {
            TurnResult::Committed { .. } => Ok(()),
            TurnResult::Rejected { reason, at_action } => {
                Err(format!("turn rejected: {reason} (at {at_action:?})"))
            }
            other => Err(format!("turn not committed: {other:?}")),
        }
    }
}

/// The inspector card's published affordances: `(name, slot)`. Each fires a real `SetField`
/// turn bumping its bound slot — so the rendered `Button` advances a live `Bind` row. The
/// names are the `data-turn` payloads the web renderer puts on the buttons.
const AFFORDANCES: [(&str, usize); 3] = [("tick", 0), ("add", 1), ("score", 2)];

/// Map an affordance name to the model slot it advances (the inverse of [`AFFORDANCES`]).
fn affordance_slot(name: &str) -> Option<usize> {
    AFFORDANCES
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, slot)| *slot)
}

/// **Generate the inspector view-tree JSON from a focused cell's live faces** — the gpui-free,
/// deos-js-free port of `deos_js::inspector_card::inspector_view_for`. Reads the RawFields +
/// Affordances faces of `id` off `rt`'s ledger via [`deos_reflect`] and lifts them into the
/// `{kind, props, children}` view-tree JSON the web renderer (`deos-view::parse_view_tree`)
/// consumes: a titled column with a RawFields section (a live `Bind` per revealed scalar slot,
/// a labeled `Text` per structural substance) and an Affordances section (a `Button` per
/// cap-gated affordance the holder of `held` may fire). The SAME shape the native inspector
/// generates — proven renderer-independent by feeding it to the web renderer.
fn inspector_view_tree_json(
    rt: &DreggRuntime,
    id: dregg_types::CellId,
    held: &AuthRequired,
    affordance_specs: &[(String, AuthRequired)],
) -> String {
    use serde_json::json;

    let mut children: Vec<serde_json::Value> = Vec::new();

    // Title.
    children.push(json!({ "kind": "text", "props": { "text": "Inspector" } }));

    // ── RawFields face ──────────────────────────────────────────────────────────────────
    let mut raw_rows: Vec<serde_json::Value> =
        vec![json!({ "kind": "text", "props": { "text": "Cell State" } })];
    if let Some(reflected) = ReflectedCell::from_ledger(&rt.ledger, id) {
        if let deos_reflect::present::PresentationBody::Fields(insp) = &reflected.raw_fields().body
        {
            for f in &insp.fields {
                match &f.value {
                    // A revealed scalar slot → a LIVE binding (re-read off the ledger, so a
                    // turn that writes the slot updates the displayed row in place).
                    FieldValue::FieldSlot { index, .. } => raw_rows.push(json!({
                        "kind": "bind",
                        "props": { "slot": *index, "label": format!("{}: ", f.key) }
                    })),
                    // The structural substances render as static labeled text.
                    FieldValue::Balance(b) => raw_rows
                        .push(json!({ "kind": "text", "props": { "text": format!("{}: {}", f.key, b) } })),
                    FieldValue::Count(c) => raw_rows
                        .push(json!({ "kind": "text", "props": { "text": format!("{}: {}", f.key, c) } })),
                    FieldValue::Bool(b) => raw_rows
                        .push(json!({ "kind": "text", "props": { "text": format!("{}: {}", f.key, b) } })),
                    FieldValue::Text(t) => raw_rows
                        .push(json!({ "kind": "text", "props": { "text": format!("{}: {}", f.key, t) } })),
                    FieldValue::Id(id) => raw_rows.push(
                        json!({ "kind": "text", "props": { "text": format!("{}: {}", f.key, short_hex(id)) } }),
                    ),
                    FieldValue::Hash(h) => raw_rows.push(
                        json!({ "kind": "text", "props": { "text": format!("{}: {}", f.key, short_hex(h)) } }),
                    ),
                    FieldValue::CapEdge { target, slot } => raw_rows.push(json!({
                        "kind": "text",
                        "props": { "text": format!("{}: → {} @{}", f.key, short_hex(target), slot) }
                    })),
                    FieldValue::CommittedSlot { index, .. } => raw_rows.push(json!({
                        "kind": "text",
                        "props": { "text": format!("{}: state[{}] ⟨committed⟩", f.key, index) }
                    })),
                }
            }
        }
    }
    children.push(json!({ "kind": "vstack", "props": {}, "children": raw_rows }));

    // ── Affordances face ────────────────────────────────────────────────────────────────
    let mut aff_rows: Vec<serde_json::Value> =
        vec![json!({ "kind": "text", "props": { "text": "Affordances" } })];
    let mut surface = AffordanceSurface::new(id);
    for (name, required) in affordance_specs {
        surface = surface.declare(deos_reflect::Affordance::new(
            name.clone(),
            required.clone(),
            Effect::IncrementNonce { cell: id },
        ));
    }
    for aff in surface.project_for(held) {
        aff_rows.push(json!({
            "kind": "button",
            "props": { "label": aff.name.clone(), "on_click": { "turn": aff.name.clone(), "arg": 1 } }
        }));
    }
    children.push(json!({ "kind": "vstack", "props": {}, "children": aff_rows }));

    serde_json::Value::Object(
        [
            ("kind".to_string(), json!("vstack")),
            ("props".to_string(), json!({})),
            ("children".to_string(), json!(children)),
        ]
        .into_iter()
        .collect(),
    )
    .to_string()
}

/// A short legible id (first 6 hex … last 4) for a static field row — mirrors the native
/// inspector's `short_id`.
fn short_hex(bytes: &[u8; 32]) -> String {
    let h: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
    format!("{}…{}", &h[..6], &h[h.len() - 4..])
}

// ════════════════════════════════════════════════════════════════════════════════════════
//  THE TALLY-BOARD CARD, IN THE TAB — exercising the FULL ViewNode vocabulary
// ════════════════════════════════════════════════════════════════════════════════════════
//
// `CardWorld` (one slot, one affordance) and `InspectorWorld` (several slots, one affordance
// each) drive a `vstack` of `text`/`bind`/`button`. Neither exercises the view-tree's
// LAYOUT nodes (`Row`, `Table`) nor more than one affordance per slot — yet `deos-view`'s
// web renderer paints all of them. The TALLY BOARD does: it is a `table` of `row`s, each row
// a named tally with its live `bind` value AND two affordances (`+1` / `-1`). So a click on
// EITHER button is a real cap-gated verified turn that moves that one tally up or down, and
// the bound row re-paints — proving `Row` + `Table` + multi-affordance cards render AND fire
// in a browser tab through the SAME ViewNode IR the native cockpit renders.
//
// Like the inspector this rests entirely on the embedded `DreggEngine` (no `mozjs` on
// wasm32): each tally is a model slot; `+1`/`-1` are `SetField + IncrementNonce` turns over
// the canonical executor, leaving real receipts. The affordance `data-arg` carries the SLOT
// index (which tally the button moves) and `data-turn` the direction (`inc`/`dec`).

/// The tally board's named rows — one model slot each. The label heads each `row`; the slot
/// index is what a button's `data-arg` carries (the inverse: slot → its rendered label).
const TALLY_LABELS: [&str; 3] = ["apples", "oranges", "pears"];

/// The tally-board card, driven from the browser tab over its own embedded verified executor.
/// One `TallyWorld` owns one runtime with one tally-cell (agent 0); each tally is a model slot
/// and each `+1`/`-1` click fires a REAL cap-gated verified turn — the wasm realization of a
/// multi-row, multi-affordance deos-js card over the full `Row`/`Table` ViewNode vocabulary.
#[wasm_bindgen]
pub struct TallyWorld {
    rt: DreggRuntime,
}

#[wasm_bindgen]
impl TallyWorld {
    /// Mint a fresh tally board on its own embedded executor, seeding each tally slot. The
    /// tally-cell is agent 0 (single-custody, `AuthRequired::None` holder — the posture
    /// `Applet::mint` gives a card), funded so a metered turn has a source. `seeds[i]` seeds
    /// tally `i` (defaults to a clearly-distinct `[3, 1, 4]`); each non-zero seed is committed
    /// via a REAL verified turn, so the genesis board itself leaves receipts.
    #[wasm_bindgen(constructor)]
    pub fn new(seeds: Vec<u64>) -> Result<TallyWorld, JsError> {
        let mut rt = DreggRuntime::new();
        rt.try_create_agent("tally", 1_000_000)
            .map_err(|e| JsError::new(&e))?;
        let mut world = TallyWorld { rt };
        let defaults = [3u64, 1u64, 4u64];
        for slot in 0..TALLY_LABELS.len() {
            let value = seeds.get(slot).copied().unwrap_or(defaults[slot]);
            if value != 0 {
                world
                    .commit_set(slot, value)
                    .map_err(|e| JsError::new(&e))?;
            }
        }
        Ok(world)
    }

    /// The tally-cell's id (hex) — the sovereignty boundary, the agent of its turns.
    #[wasm_bindgen(js_name = cellId)]
    pub fn cell_id(&self) -> String {
        crate::bindings::hex_encode(&self.rt.agents[0].cell_id.0)
    }

    /// A witnessed read of tally `slot` off the live ledger — the value the web renderer
    /// paints into the matching `data-slot` span (the SAME read each row's `bind` makes).
    pub fn read(&self, slot: usize) -> u64 {
        let cell_id = self.rt.agents[0].cell_id;
        self.rt
            .cell_field(&cell_id, slot)
            .map(|fe| unpack_u64(&fe))
            .unwrap_or(0)
    }

    /// The committed-receipt count — the audit tape length (one per fired turn, plus the
    /// genesis seeds). A browser shows it to prove a `+1`/`-1` was a real turn, not a poke.
    #[wasm_bindgen(js_name = receiptCount)]
    pub fn receipt_count(&self) -> usize {
        self.rt.receipts.len()
    }

    /// **THE TALLY VIEW-TREE** — a `table` of `row`s, one per named tally: each row carries a
    /// `text` label, a live `bind` of that tally's slot, and `+1`/`-1` affordance `button`s.
    /// The SAME `{kind, props, children}` JSON the web renderer (`deos-view::parse_view_tree`)
    /// consumes — serve it and the board paints live in a browser.
    #[wasm_bindgen(js_name = viewTreeJson)]
    pub fn view_tree_json(&self) -> String {
        tally_view_tree_json()
    }

    /// **Move one tally** — commit ONE cap-gated verified turn: the tally `arg` advances or
    /// retreats by one (`turn` = `"inc"`/`"dec"`), then return the re-read value (the new
    /// `bind` value the browser re-paints). `arg` is the SLOT index the button carried as
    /// `data-arg`. A `dec` saturates at 0; an unknown direction or out-of-range slot commits
    /// nothing and errors (the native `FireError::Unknown`).
    pub fn fire(&mut self, turn: &str, arg: i32) -> Result<u64, JsError> {
        let slot = arg as usize;
        if slot >= TALLY_LABELS.len() {
            return Err(JsError::new(&format!("tally slot out of range: {slot}")));
        }
        let current = self.read(slot);
        let next = match turn {
            "inc" => current.saturating_add(1),
            "dec" => current.saturating_sub(1),
            other => return Err(JsError::new(&format!("unknown affordance: {other}"))),
        };
        self.commit_set(slot, next).map_err(|e| JsError::new(&e))?;
        Ok(self.read(slot))
    }

    /// Commit `slot := value` on the tally cell as a REAL verified turn (`SetField` +
    /// `IncrementNonce` — the SAME two effects `Applet::fire` builds), routed through
    /// `execute_turn_for_agent`. A rejected turn is surfaced, never swallowed.
    fn commit_set(&mut self, slot: usize, value: u64) -> Result<(), String> {
        let cell_id = self.rt.agents[0].cell_id;
        let effects = vec![
            Effect::SetField {
                cell: cell_id,
                index: slot,
                value: pack_u64(value),
            },
            Effect::IncrementNonce { cell: cell_id },
        ];
        match self.rt.execute_turn_for_agent(0, effects, 10_000) {
            TurnResult::Committed { .. } => Ok(()),
            TurnResult::Rejected { reason, at_action } => {
                Err(format!("turn rejected: {reason} (at {at_action:?})"))
            }
            other => Err(format!("turn not committed: {other:?}")),
        }
    }
}

/// Generate the tally board's view-tree JSON: a titled column over a `table` of `row`s, one
/// per [`TALLY_LABELS`] entry. Each row is `row(text(label), bind(slot), button("+1"), button("−1"))`
/// — the `+1`/`−1` buttons carry `data-turn=inc/dec` and `data-arg=slot`. This is the
/// substance: `Row` + `Table` + multi-affordance, all through the SAME ViewNode vocabulary
/// the native renderer walks into gpui widgets.
fn tally_view_tree_json() -> String {
    use serde_json::json;

    let mut rows: Vec<serde_json::Value> = Vec::new();
    for (slot, label) in TALLY_LABELS.iter().enumerate() {
        rows.push(json!({
            "kind": "row",
            "props": {},
            "children": [
                { "kind": "text", "props": { "text": format!("{label}: ") } },
                { "kind": "bind", "props": { "slot": slot, "label": "" } },
                { "kind": "button", "props": { "label": "+1", "on_click": { "turn": "inc", "arg": slot } } },
                { "kind": "button", "props": { "label": "−1", "on_click": { "turn": "dec", "arg": slot } } }
            ]
        }));
    }

    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            { "kind": "text", "props": { "text": "Tally board" } },
            { "kind": "table", "props": {}, "children": rows }
        ]
    })
    .to_string()
}
