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
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};

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

/// Collect the model `slot` of every `bind` node in a view-tree JSON, in
/// tree-walk (pre-order) appearance — the SAME order `deos_view::web::render_html`
/// mints its positional `BindValues` cursor. A world builds its `render_html`
/// bind-value vector by reading each of these slots off its live ledger, so the
/// painted value under each `bind` span is the witnessed committed value (exactly
/// what the served live bootstrap re-reads JS-side after boot). Walks the `children`
/// arrays the deos-js vocabulary uses (`vstack`/`row`/`list`/`table`/…).
fn bind_slots_in_order(view_tree_json: &str) -> Vec<usize> {
    fn walk(v: &serde_json::Value, out: &mut Vec<usize>) {
        match v {
            serde_json::Value::Object(map) => {
                if map.get("kind").and_then(|k| k.as_str()) == Some("bind") {
                    let slot = map
                        .get("props")
                        .and_then(|p| p.get("slot"))
                        .and_then(|s| s.as_u64())
                        .unwrap_or(0) as usize;
                    out.push(slot);
                }
                if let Some(children) = map.get("children") {
                    walk(children, out);
                }
            }
            serde_json::Value::Array(arr) => {
                for it in arr {
                    walk(it, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    if let Ok(v) = serde_json::from_str::<serde_json::Value>(view_tree_json) {
        walk(&v, &mut out);
    }
    out
}

/// **Render a world's view-tree to an HTML fragment IN-WASM** — the gpui-free web
/// projection, in the tab. Parses `view_tree_json` with the SAME
/// `deos_view::parse_view_tree` the native path uses, builds the positional
/// `BindValues` by reading each `bind` node's slot off the live ledger (`read_slot`),
/// and walks the tree through `deos_view::web::render_html` (the IDENTICAL renderer the
/// server bake runs). A Custom Element does `shadowRoot.innerHTML = world.render_html()`
/// and repaints after each `fire`. Byte-identical to the server bake for the same tree +
/// committed values.
fn render_world_html(view_tree_json: &str, read_slot: impl Fn(usize) -> u64) -> String {
    let tree = match deos_view::parse_view_tree(view_tree_json) {
        Ok(t) => t,
        Err(e) => return format!("<pre class=\"deos-text\">view-tree error: {e}</pre>"),
    };
    let binds: Vec<u64> = bind_slots_in_order(view_tree_json)
        .into_iter()
        .map(read_slot)
        .collect();
    deos_view::render_html(&tree, &binds)
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

    /// **THE COUNTER CARD'S VIEW-TREE** — byte-for-byte the shape the SpiderMonkey engine
    /// produces for the counter card (`deos.ui.vstack(text, bind, button)`): a titled column
    /// with a live `bind` of the bound `slot` and a `+1` affordance `button`
    /// (`{turn:"inc", arg:1}`). The SAME `{kind, props, children}` JSON the web renderer
    /// (`deos-view::parse_view_tree`) consumes — [`Self::render_html`] walks it in-tab.
    #[wasm_bindgen(js_name = viewTreeJson)]
    pub fn view_tree_json(&self) -> String {
        use serde_json::json;
        json!({
            "kind": "vstack",
            "props": {},
            "children": [
                { "kind": "text", "props": { "text": "Counter applet" } },
                { "kind": "bind", "props": { "slot": self.slot, "label": "count: " } },
                { "kind": "button", "props": { "label": "+1", "on_click": { "turn": "inc", "arg": 1 } } }
            ]
        })
        .to_string()
    }

    /// **RENDER THE COUNTER CARD TO HTML, IN-WASM** — [`Self::view_tree_json`] walked through
    /// the gpui-free web renderer (`deos-view::render_html`), the live `bind` painted from the
    /// committed slot ([`Self::read`]). A Custom Element sets this as its shadow root's
    /// `innerHTML` and re-calls it after each `fire` to repaint. Byte-identical to the server
    /// bake of the counter card at the same committed value.
    #[wasm_bindgen(js_name = renderHtml)]
    pub fn render_html(&self) -> String {
        render_world_html(&self.view_tree_json(), |_slot| self.read())
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

    /// **RENDER THE INSPECTOR CARD TO HTML, IN-WASM** — [`Self::view_tree_json`] walked through
    /// the gpui-free web renderer, each live `Bind` row painted from its own slot off the
    /// committed ledger ([`Self::read`]). The Custom Element repaints via this after each fire.
    #[wasm_bindgen(js_name = renderHtml)]
    pub fn render_html(&self) -> String {
        render_world_html(&self.view_tree_json(), |slot| self.read(slot))
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

    /// **RENDER THE TALLY BOARD TO HTML, IN-WASM** — [`Self::view_tree_json`] (a `Table` of
    /// `Row`s) walked through the gpui-free web renderer, each row's live `bind` painted from
    /// its own tally slot off the committed ledger ([`Self::read`]). The Custom Element repaints
    /// via this after each `+1`/`−1` fire.
    #[wasm_bindgen(js_name = renderHtml)]
    pub fn render_html(&self) -> String {
        render_world_html(&self.view_tree_json(), |slot| self.read(slot))
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

// ════════════════════════════════════════════════════════════════════════════════════════
//  THE KV-STORE SERVICE CELL, IN THE TAB — a published interface invoked client-side
// ════════════════════════════════════════════════════════════════════════════════════════
//
// `CardWorld`/`InspectorWorld`/`TallyWorld` drive a cell's OWN slots through bare `SetField`
// turns. The KV-STORE is a different deos surface: a **service cell** that publishes a
// first-class typed `InterfaceDescriptor` (`put` · `delete` · `get`) and whose method calls
// are ROUTED through the verified DFA router before they desugar to the ordinary `SetField`
// effects the kernel already enforces. There is NO `Effect::Invoke` — the kernel and the
// light client keep seeing only the `SetField`s they witness; the one extra fact, that an
// invoked method is a member of the cell's interface, is decided by the SAME
// `InterfaceDescriptor::route_method` (a `dregg_dfa::Router`) the protocol uses.
//
// This is the wasm realization of `starbridge_kvstore` (the crate itself can't be a wasm dep:
// it pulls `dregg-app-framework` → axum/tokio/reqwest, so its program VALUE lives in
// `runtime::app_programs::kvstore_program`, exactly as the subscription/governance programs
// do, and its `invoke()` routing core — route → gate-serviced → cap-gate → desugar — is
// re-expressed here over the SAME `dregg_cell::interface` types). Every `put`/`delete` is a
// REAL cap-gated verified turn whose post-state the executor checks against the store's
// `CellProgram`. The store program scopes `StateConstraint::Monotonic` on the VERSION slot to
// the `put`/`delete` cases — so a replay/reorder that would lower the version is an EXECUTOR
// REFUSAL, here in the tab (`try_rollback` exercises it). `get` is `Serviced` — its answer
// rides the OFE cross-cell-read, not a replay desugar — so the router REFUSES to desugar it,
// naming the seam honestly rather than faking a write (`try_get`).

/// The number of value registers the KV-store card surfaces as live rows (slots
/// [`app_programs::KV_REG_MIN`]`..`). The store itself addresses `REG_MIN..=REG_MAX`; the card
/// shows the first few as a legible register file.
const KV_REGS_SHOWN: usize = 4;

/// The fee (computrons) each `put`/`delete` turn meters against the caller's cell.
const KV_FEE: u64 = 10_000;

/// **The store's published typed interface** — the wasm mirror of
/// `starbridge_kvstore::interface_descriptor`: `put(reg, value)` and `delete(reg)` are
/// `Signature`-gated `Replayable` mutators; `get(reg)` is a `Serviced` read (the named OFE
/// seam, never desugared). Routed through the SAME `dregg_dfa` router the protocol uses.
fn kv_interface_descriptor() -> InterfaceDescriptor {
    InterfaceDescriptor::new(vec![
        MethodSig {
            args_schema: ArgsSchema::Fixed(2),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol("put"))
        },
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol("delete"))
        },
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol("get"))
        },
    ])
}

/// Pack a `u64` into the CANONICAL felt lane the executor's state constraints read — bytes
/// `[24..32]`, big-endian (the same `dregg_app_framework::field_from_u64` /
/// `program::eval::field_to_u64` use). The store's `Monotonic` version check operates on THIS
/// lane, so the KV-store writes + reads it (not the deos-js applet's little-endian low-8 lane
/// the counter/tally use for their own bare slots).
fn fe_be(v: u64) -> [u8; 32] {
    let mut fe = [0u8; 32];
    fe[24..32].copy_from_slice(&v.to_be_bytes());
    fe
}

/// Read a `u64` back out of the canonical felt lane (`[24..32]`, big-endian) — the inverse of
/// [`fe_be`], matching the executor's `field_to_u64`.
fn be_to_u64(fe: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[24..32]);
    u64::from_be_bytes(b)
}

/// The KV-store service cell, driven from the browser tab. A `KvStoreWorld` owns one runtime
/// with a CALLER agent (agent 0, the signer/fee-payer) and a separate STORE cell carrying the
/// published interface + the verified `CellProgram`. Each `put`/`delete` affordance is ROUTED
/// through the store's `InterfaceDescriptor` and fired as a REAL cap-gated verified turn
/// against the store cell — the wasm realization of `starbridge_kvstore` over a live World.
#[wasm_bindgen]
pub struct KvStoreWorld {
    rt: DreggRuntime,
    /// The store cell — the service object the caller invokes methods on.
    store: dregg_types::CellId,
    /// The store's published typed interface (the routing front door).
    descriptor: InterfaceDescriptor,
}

#[wasm_bindgen]
impl KvStoreWorld {
    /// Mint a KV-store on its own embedded executor: a caller agent (the signer), a store cell
    /// owned by a distinct synthetic key with the [`app_programs::kvstore_program`] installed
    /// (open permissions; the verified slot-caveat is the enforcement), and a reach capability
    /// granted to the caller. `seeds[i]` seeds register [`app_programs::KV_REG_MIN`]`+ i` via a
    /// REAL `put` invocation (each routes through the interface and bumps the version), so the
    /// genesis store itself leaves receipts. Pass an empty/short array for the defaults.
    #[wasm_bindgen(constructor)]
    pub fn new(seeds: Vec<u64>) -> Result<KvStoreWorld, JsError> {
        use crate::runtime::app_programs;
        let mut rt = DreggRuntime::new();
        // The caller: agent 0, the signer + fee-payer for every put/delete turn.
        rt.try_create_agent("kvstore-caller", 2_000_000)
            .map_err(|e| JsError::new(&e))?;
        // The store cell, owned by a synthetic key distinct from the caller's (so its id does
        // not collide with the caller's own cell), with the verified store program installed.
        let store_owner = *blake3::hash(b"dregg-wasm-kvstore-owner").as_bytes();
        let store = rt
            .mint_cell_from_genesis(store_owner, 0)
            .map_err(|e| JsError::new(&e))?;
        rt.install_app_program(
            &store,
            app_programs::kvstore_program(),
            app_programs::kvstore_initial_state(),
        )
        .map_err(|e| JsError::new(&e))?;
        // The caller must hold a capability to REACH the store (a non-self target).
        rt.grant_reach_capability(0, store)
            .map_err(|e| JsError::new(&e))?;
        let mut world = KvStoreWorld {
            rt,
            store,
            descriptor: kv_interface_descriptor(),
        };
        let defaults = [10u64, 20u64, 30u64, 40u64];
        for i in 0..KV_REGS_SHOWN {
            let reg = app_programs::KV_REG_MIN as usize + i;
            let value = seeds.get(i).copied().unwrap_or(defaults[i]);
            if value != 0 {
                // Seed through the REAL put front door (routes + bumps the version).
                world
                    .put(reg as i32, value as i32)
                    .map_err(|e| JsError::new(&format!("seed put failed: {e:?}")))?;
            }
        }
        Ok(world)
    }

    /// The store cell's id (hex) — the service object's sovereignty boundary.
    #[wasm_bindgen(js_name = cellId)]
    pub fn cell_id(&self) -> String {
        crate::bindings::hex_encode(&self.store.0)
    }

    /// A witnessed read of store slot `slot` off the live ledger (the canonical felt lane). The
    /// value the web renderer paints into the matching `data-slot` span — slot 0 is the version,
    /// slots `REG_MIN..` the registers.
    pub fn read(&self, slot: usize) -> u64 {
        self.rt
            .cell_field(&self.store, slot)
            .map(|fe| be_to_u64(&fe))
            .unwrap_or(0)
    }

    /// The store's monotone version (slot 0) — bumped by every committed `put`/`delete`, and
    /// (by the verified `Monotonic` constraint) never able to roll back.
    pub fn version(&self) -> u64 {
        use crate::runtime::app_programs;
        self.read(app_programs::KV_VERSION_SLOT as usize)
    }

    /// The committed-receipt count — the audit tape length (one per committed method turn,
    /// including the genesis seed puts).
    #[wasm_bindgen(js_name = receiptCount)]
    pub fn receipt_count(&self) -> usize {
        self.rt.receipts.len()
    }

    /// The published interface as JSON (`[{name, auth, semantics, arity}]`) — what the Service
    /// Explorer resolves. The card shows it so a visitor sees the typed contract the affordances
    /// route through.
    #[wasm_bindgen(js_name = methodsJson)]
    pub fn methods_json(&self) -> String {
        use serde_json::json;
        let rows: Vec<serde_json::Value> = [("put", "Signature"), ("delete", "Signature"), ("get", "None")]
            .iter()
            .filter_map(|(name, auth)| {
                self.descriptor.method(&method_symbol(name)).map(|m| {
                    json!({
                        "name": name,
                        "auth": auth,
                        "semantics": if m.semantics == Semantics::Serviced { "serviced" } else { "replayable" },
                    })
                })
            })
            .collect();
        json!(rows).to_string()
    }

    /// **THE KV-STORE VIEW-TREE** — a titled column with the version row and a `table` of
    /// register rows, each `row(text(label), bind(slot), button("put"), button("del"))`. The
    /// `put`/`del` buttons carry `data-turn=put/delete` and `data-arg=slot` (the register index)
    /// — the SAME `{kind, props, children}` JSON the web renderer (`deos-view`) consumes.
    #[wasm_bindgen(js_name = viewTreeJson)]
    pub fn view_tree_json(&self) -> String {
        kvstore_view_tree_json()
    }

    /// **RENDER THE KV-STORE CARD TO HTML, IN-WASM** — [`Self::view_tree_json`] (the version row
    /// + a `Table` of register rows) walked through the gpui-free web renderer, each live `bind`
    /// painted from its own slot off the committed ledger ([`Self::read`] over the canonical
    /// big-endian felt lane). The Custom Element repaints via this after each `put`/`del` fire.
    #[wasm_bindgen(js_name = renderHtml)]
    pub fn render_html(&self) -> String {
        render_world_html(&self.view_tree_json(), |slot| self.read(slot))
    }

    /// **Invoke `put(reg)`** — write `reg := reg + 1` (a single-arg-friendly bump) and bump the
    /// store version by one, as a REAL cap-gated verified turn ROUTED through the published
    /// interface. Returns the re-read register value. `value` (when ≥ 0) overrides the written
    /// value (used by the seed path); a negative `value` means "bump the current register".
    pub fn put(&mut self, reg: i32, value: i32) -> Result<u64, JsError> {
        let reg = reg as usize;
        let write = if value >= 0 {
            value as u64
        } else {
            self.read(reg).saturating_add(1)
        };
        let new_version = self.version().saturating_add(1);
        let effects = self.desugar_mutator("put", reg, write, new_version)?;
        self.commit_method("put", effects)?;
        Ok(self.read(reg))
    }

    /// **Invoke `delete(reg)`** — clear `reg` to zero and bump the store version, as a REAL
    /// cap-gated verified turn routed through the interface. Returns the re-read value (0).
    pub fn delete(&mut self, reg: i32) -> Result<u64, JsError> {
        let reg = reg as usize;
        let new_version = self.version().saturating_add(1);
        let effects = self.desugar_mutator("delete", reg, 0, new_version)?;
        self.commit_method("delete", effects)?;
        Ok(self.read(reg))
    }

    /// **The affordance wire entry** — the web renderer fires `data-turn`/`data-arg` here.
    /// `put`/`delete` route + commit; any other name errors (the native `FireError::Unknown`).
    /// `arg` is the register index the button carried.
    pub fn fire(&mut self, turn: &str, arg: i32) -> Result<u64, JsError> {
        match turn {
            "put" => self.put(arg, -1),
            "delete" => self.delete(arg),
            other => Err(JsError::new(&format!("unknown affordance: {other}"))),
        }
    }

    /// **Prove the verified guarantee BITES in the tab** — attempt a `put` that LOWERS the
    /// store version (a replay/rollback), which the store program's `Monotonic` version
    /// constraint must REFUSE on the verified commit path. Returns JSON
    /// `{refused: bool, reason: string}`; `refused: true` is the witnessed enforcement. (Needs
    /// the version already ≥ 1 — seed the store first.)
    #[wasm_bindgen(js_name = tryRollback)]
    pub fn try_rollback(&mut self, reg: i32) -> String {
        use serde_json::json;
        let reg = reg as usize;
        let current = self.version();
        if current == 0 {
            return json!({ "refused": false, "reason": "version is 0 — nothing to roll back" })
                .to_string();
        }
        let stale_version = current - 1; // strictly lower → must be refused
        let effects = match self.desugar_mutator("put", reg, self.read(reg), stale_version) {
            Ok(e) => e,
            Err(e) => return json!({ "refused": false, "reason": format!("{e:?}") }).to_string(),
        };
        match self
            .rt
            .execute_app_turn_for_agent(0, self.store, "put", effects, KV_FEE)
        {
            Ok(dregg_turn::TurnResult::Rejected { reason, .. }) => {
                json!({ "refused": true, "reason": format!("{reason}") }).to_string()
            }
            Ok(dregg_turn::TurnResult::Committed { receipt, .. }) => {
                // It should NOT have committed — surface the breach honestly.
                self.rt.receipts.push(receipt);
                json!({ "refused": false, "reason": "rollback COMMITTED — Monotonic did not bite!" })
                    .to_string()
            }
            Ok(other) => json!({ "refused": false, "reason": format!("{other:?}") }).to_string(),
            Err(e) => json!({ "refused": false, "reason": e }).to_string(),
        }
    }

    /// **Prove `get` is a NAMED SEAM, not a faked write** — route `get(reg)` through the
    /// interface; because it is `Semantics::Serviced` its answer rides the OFE cross-cell-read,
    /// so the router REFUSES to desugar it to a turn. Returns the refusal message (the honest
    /// seam), or — never reached for a correct descriptor — an error if `get` somehow desugared.
    #[wasm_bindgen(js_name = tryGet)]
    pub fn try_get(&self, reg: i32) -> String {
        let _ = reg;
        match self.descriptor.route_method(&method_symbol("get")) {
            Some(sig) if sig.semantics == Semantics::Serviced => {
                "get is a Serviced method; its answer rides the OFE cross-cell-read (named seam) \
                 — no effect desugar"
                    .to_string()
            }
            Some(_) => "get unexpectedly resolved as replayable (descriptor bug)".to_string(),
            None => "get is not a declared method (descriptor bug)".to_string(),
        }
    }

    // ── internals ───────────────────────────────────────────────────────────────────────

    /// Route a mutator (`put`/`delete`) through the published interface and DESUGAR it to the
    /// underlying `SetField` effects (version bump + the register write) — the wasm mirror of
    /// `starbridge_kvstore`'s `invoke()` core: route via the verified DFA, refuse a `Serviced`
    /// seam, then build the effects the kernel already enforces. No `Effect::Invoke`.
    fn desugar_mutator(
        &self,
        method: &str,
        reg: usize,
        value: u64,
        new_version: u64,
    ) -> Result<Vec<Effect>, JsError> {
        use crate::runtime::app_programs;
        if !(app_programs::KV_REG_MIN as usize..=app_programs::KV_REG_MAX as usize).contains(&reg) {
            return Err(JsError::new(&format!(
                "register {reg} is not a valid key (expected {}..={})",
                app_programs::KV_REG_MIN,
                app_programs::KV_REG_MAX
            )));
        }
        // (1) Route through the VERIFIED DFA router (the same the protocol uses).
        let sig = self
            .descriptor
            .route_method(&method_symbol(method))
            .ok_or_else(|| JsError::new(&format!("method `{method}` is not declared")))?;
        // (2) A Serviced method does not desugar to a replay effect — named seam.
        if sig.semantics == Semantics::Serviced {
            return Err(JsError::new(&format!(
                "method `{method}` is Serviced — answered by the OFE read, not a turn"
            )));
        }
        // (3) Desugar to the underlying SetFields: bump the version + write the register.
        Ok(vec![
            Effect::SetField {
                cell: self.store,
                index: app_programs::KV_VERSION_SLOT as usize,
                value: fe_be(new_version),
            },
            Effect::SetField {
                cell: self.store,
                index: reg,
                value: fe_be(value),
            },
        ])
    }

    /// Commit a routed method's desugared effects as a REAL signed turn TARGETING the store
    /// cell with `method`'s symbol (so the store program's `MethodIs` guard dispatches the right
    /// `Monotonic`-version case). A rejected turn is surfaced, never swallowed.
    fn commit_method(&mut self, method: &str, effects: Vec<Effect>) -> Result<(), JsError> {
        match self
            .rt
            .execute_app_turn_for_agent(0, self.store, method, effects, KV_FEE)
        {
            Ok(TurnResult::Committed { .. }) => Ok(()),
            Ok(TurnResult::Rejected { reason, at_action }) => Err(JsError::new(&format!(
                "turn rejected: {reason} (at {at_action:?})"
            ))),
            Ok(other) => Err(JsError::new(&format!("turn not committed: {other:?}"))),
            Err(e) => Err(JsError::new(&e)),
        }
    }
}

/// Generate the KV-store view-tree JSON: a titled column with a version `row` and a `table` of
/// register rows. Each register row is `row(text(label), bind(slot), button("put"),
/// button("del"))` — `put`/`del` carry `data-turn=put/delete` + `data-arg=slot`. The SAME
/// ViewNode vocabulary the native cockpit renders, here for a SERVICE-CELL surface.
fn kvstore_view_tree_json() -> String {
    use crate::runtime::app_programs;
    use serde_json::json;

    let mut reg_rows: Vec<serde_json::Value> = Vec::new();
    for i in 0..KV_REGS_SHOWN {
        let slot = app_programs::KV_REG_MIN as usize + i;
        reg_rows.push(json!({
            "kind": "row",
            "props": {},
            "children": [
                { "kind": "text", "props": { "text": format!("reg {slot}: ") } },
                { "kind": "bind", "props": { "slot": slot, "label": "" } },
                { "kind": "button", "props": { "label": "put", "on_click": { "turn": "put", "arg": slot } } },
                { "kind": "button", "props": { "label": "del", "on_click": { "turn": "delete", "arg": slot } } }
            ]
        }));
    }

    json!({
        "kind": "vstack",
        "props": {},
        "children": [
            { "kind": "text", "props": { "text": "Key-Value Store — service cell" } },
            { "kind": "text", "props": { "text": "a published interface (put · delete · get) routed through the verified DFA" } },
            { "kind": "row", "props": {}, "children": [
                { "kind": "text", "props": { "text": "store version: " } },
                { "kind": "bind", "props": { "slot": app_programs::KV_VERSION_SLOT as usize, "label": "" } }
            ] },
            { "kind": "table", "props": {}, "children": reg_rows }
        ]
    })
    .to_string()
}

// ════════════════════════════════════════════════════════════════════════════════════════
//  THE COLLECTIVE-CHOICE POLL, IN THE TAB — a real quorum-gated one-vote-per-ballot vote
// ════════════════════════════════════════════════════════════════════════════════════════
//
// `CardWorld`/`TallyWorld` move a cell's slots through bare `SetField` turns — a counter, not
// a vote. `PollWorld` is the REAL `collective-choice` engine's shape as an in-tab world: a
// quorum-gated, one-vote-per-ballot, monotone-tally vote where each `cast` is a genuine
// cap-gated verified turn (a ballot's `WriteOnce(VOTE)` write + a poll cell's `Monotonic`
// tally bump), the decision-turn is gated by the polis `AffineLe` quorum, and the tally is
// light-client-recomputable from the append-only cast log.
//
// ── WHY A TRIMMED (BUT REAL) SHAPE, NOT THE `collective-choice` CRATE ────────────────────
// The `collective-choice` crate CANNOT be a wasm32 dependency: its `CollectiveChoice` engine
// is built on `dregg_app_framework::EmbeddedExecutor`, and `dregg-app-framework` depends on
// `axum` + `tokio` (features = ["full"]) + `reqwest` + `tower-http` — none of which compile
// to `wasm32-unknown-unknown` (server I/O, native sockets). This is the SAME wall the wasm
// Cargo.toml already names for `starbridge-kvstore`/`-subscription`/`-governed-namespace`.
//
// So — exactly as `KvStoreWorld` re-materialises the kvstore program VALUE over the wasm
// `DreggRuntime` executor rather than depending on the axum-bound crate — `PollWorld`
// re-expresses `collective-choice`'s four proven mechanisms over the SAME wasm-compatible
// `TurnExecutor`, keeping every tooth REAL (the identical `StateConstraint` turn shapes the
// executor re-enforces on the verified commit path, mirroring `CollectiveChoice::poll_program`
// + `starbridge_privacy_voting`'s ballot `WriteOnce(VOTE)`):
//   (i)   one-vote-per-ballot : each voter's ballot cell carries `WriteOnce(VOTE)` — a second
//                               vote that CHANGES the ballot's choice is an EXECUTOR REFUSAL
//                               (`try_ballot_write_once` exercises it).
//   (ii)  monotone tally      : the poll cell's per-option tallies are `Monotonic` — a stale
//                               or reordered value can never shrink the board.
//   (iii) quorum gate         : the polis `AffineLe { M·RESOLVED − Σ TALLY_i ≤ 0 }` guards the
//                               `RESOLVED` slot, so the decision-turn commits ONLY at quorum
//                               (`try_resolve`).
//   plus a one-vote nullifier set (the node's `used_proof_hashes` mirror): a consumed ballot
//   proof is refused engine-wide (the `cast` double-vote depth).
// It is a plain counter NOWHERE: every `cast` is two real verified turns, and each guarantee
// above is an executor-enforced `StateConstraint`, not a userspace `if`.

/// The ballot cell's single `WriteOnce` choice slot (the `VOTE` register). Non-zero once the
/// voter has cast (`option + 1`), frozen thereafter (a second changing write is refused).
const BALLOT_VOTE_SLOT: usize = 0;
/// The poll cell's quorum-threshold `M` slot (mirrors `collective_choice::QUORUM_M_SLOT`).
const POLL_QUORUM_M_SLOT: usize = 4;
/// The poll cell's active-option-count slot (mirrors `collective_choice::OPTION_COUNT_SLOT`).
const POLL_OPTION_COUNT_SLOT: usize = 5;
/// The poll cell's decision flag — 0 while pending, 1 once the quorum `AffineLe` certifies.
/// `WriteOnce` and gated by the quorum `AffineLe` (mirrors `collective_choice::RESOLVED_SLOT`).
const POLL_RESOLVED_SLOT: usize = 7;
/// First per-option tally slot; option `i` lives at `POLL_TALLY_BASE + i`. `Monotonic`.
const POLL_TALLY_BASE: usize = 8;
/// Ceiling on options (slots 8..16 — the 16-slot cell's structural ceiling).
const POLL_MAX_OPTIONS: usize = 8;
/// The fee (computrons) each ballot / tally / resolve turn meters against the operator cell.
const POLL_FEE: u64 = 10_000;

/// The real `collective-choice` vote, driven from the browser tab over its own embedded
/// verified executor. One `PollWorld` owns one runtime with one poll (tally-board) cell and
/// one factory-shaped ballot cell per voter; each `cast` is a genuine cap-gated verified turn
/// (a ballot `WriteOnce(VOTE)` + a poll `Monotonic` tally bump), one-vote-per-ballot enforced
/// three depths deep, the decision-turn quorum-gated by the polis `AffineLe`.
#[wasm_bindgen]
pub struct PollWorld {
    rt: DreggRuntime,
    /// The poll (tally-board) cell — the quorum-gated board every vote bumps.
    poll: dregg_types::CellId,
    /// Number of active options.
    option_count: usize,
    /// The quorum threshold `M` (the `AffineLe` coefficient); a decision certifies at `Σ ≥ M`.
    quorum_m: u64,
    /// The issued ballot cell per voter index (issued lazily; each `WriteOnce(VOTE)`).
    ballots: Vec<dregg_types::CellId>,
    /// The next fresh voter `fire("cast", …)` auto-advances to (each cast = a new ballot).
    next_voter: usize,
    /// Consumed ballot nullifiers — the `used_proof_hashes` mirror (the engine double-vote depth).
    nullifiers: std::collections::HashSet<[u8; 32]>,
    /// The append-only cast log — what the light client replays to recompute the tally.
    cast_log: Vec<usize>,
}

#[wasm_bindgen]
impl PollWorld {
    /// Open a poll over `num_options` options with quorum threshold `quorum_m`, on its own
    /// embedded executor. Mints the poll (tally-board) cell and installs the quorum-gated
    /// program (`Monotonic` tallies + `WriteOnce(RESOLVED)` + the polis quorum `AffineLe`).
    /// The operator (agent 0) signs + fee-pays every ballot / tally / resolve turn.
    #[wasm_bindgen(constructor)]
    pub fn new(num_options: usize, quorum_m: u64) -> Result<PollWorld, JsError> {
        if num_options == 0 || num_options > POLL_MAX_OPTIONS {
            return Err(JsError::new(&format!(
                "num_options must be 1..={POLL_MAX_OPTIONS}, got {num_options}"
            )));
        }
        let quorum_m = quorum_m.max(1);
        let mut rt = DreggRuntime::new();
        rt.try_create_agent("poll-operator", 1_000_000_000)
            .map_err(|e| JsError::new(&e))?;
        // The poll cell, owned by a synthetic key distinct from the operator's, with the
        // quorum-gated program installed (mirrors `collective_choice`'s `seed_poll`).
        let poll_owner = *blake3::hash(b"dregg-wasm-pollworld-poll-owner").as_bytes();
        let poll = rt
            .mint_cell_from_genesis(poll_owner, 0)
            .map_err(|e| JsError::new(&e))?;
        rt.install_app_program(
            &poll,
            Self::poll_program(quorum_m, num_options),
            Self::poll_initial_state(quorum_m, num_options),
        )
        .map_err(|e| JsError::new(&e))?;
        rt.grant_reach_capability(0, poll)
            .map_err(|e| JsError::new(&e))?;
        Ok(PollWorld {
            rt,
            poll,
            option_count: num_options,
            quorum_m,
            ballots: Vec::new(),
            next_voter: 0,
            nullifiers: std::collections::HashSet::new(),
            cast_log: Vec::new(),
        })
    }

    /// The poll cell's id (hex) — the board's sovereignty boundary, the target of tally turns.
    #[wasm_bindgen(js_name = cellId)]
    pub fn cell_id(&self) -> String {
        crate::bindings::hex_encode(&self.poll.0)
    }

    /// The number of active options in this poll.
    #[wasm_bindgen(js_name = optionCount)]
    pub fn option_count(&self) -> usize {
        self.option_count
    }

    /// A witnessed read of option `option`'s running tally off the live poll cell (the
    /// canonical big-endian felt lane the `Monotonic`/`AffineLe` constraints read).
    pub fn read(&self, option: usize) -> u64 {
        self.rt
            .cell_field(&self.poll, POLL_TALLY_BASE + option)
            .map(|fe| be_to_u64(&fe))
            .unwrap_or(0)
    }

    /// The total across all options (the running Σ TALLY the quorum gate compares to `M`).
    pub fn total(&self) -> u64 {
        (0..self.option_count).map(|i| self.read(i)).sum()
    }

    /// The executor's stored monotone tally as a JSON array `[c0, c1, …]` — the board a light
    /// client re-derives. `nobody can stuff or forge it: each vote is a verifiable turn.
    pub fn tally(&self) -> String {
        let per: Vec<u64> = (0..self.option_count).map(|i| self.read(i)).collect();
        serde_json::json!(per).to_string()
    }

    /// **THE LIGHT-CLIENT TALLY** — recompute the board from the append-only cast log ALONE
    /// (never re-reading the executor's slots), as a JSON array. A verifier that never
    /// re-executes replays the recorded casts and sums them; when this AGREES with
    /// [`Self::tally`] the board is unforged ([`Self::verified`]).
    #[wasm_bindgen(js_name = lightClientTally)]
    pub fn light_client_tally(&self) -> String {
        serde_json::json!(self.light_client_counts()).to_string()
    }

    /// **THE SELF-VERIFY** — `true` iff the executor's stored monotone tally EQUALS the
    /// light-client recompute from the cast log (the anti-stuffing check, in the tab).
    pub fn verified(&self) -> bool {
        let lc = self.light_client_counts();
        (0..self.option_count).all(|i| self.read(i) == lc[i])
    }

    /// The committed-receipt count — the audit tape length (ballot mints + every ballot /
    /// tally / resolve turn). A browser shows it to prove a cast was real, not a local poke.
    #[wasm_bindgen(js_name = receiptCount)]
    pub fn receipt_count(&self) -> usize {
        self.rt.receipts.len()
    }

    /// **The affordance wire entry** — the web renderer fires `data-turn`/`data-arg` here.
    /// `cast` casts the NEXT fresh voter's ballot for option `arg`; any other name errors.
    pub fn fire(&mut self, turn: &str, arg: i32) -> Result<u64, JsError> {
        match turn {
            "cast" => self.cast(arg),
            other => Err(JsError::new(&format!("unknown affordance: {other}"))),
        }
    }

    /// **Cast one vote for `option`** using the next fresh voter's ballot — a genuine
    /// one-vote-per-ballot turn (each successive `cast` is a distinct ballot cell, so the
    /// board grows one verified vote at a time). Returns option `option`'s re-read tally.
    pub fn cast(&mut self, option: i32) -> Result<u64, JsError> {
        let voter = self.next_voter;
        self.next_voter += 1;
        self.do_cast(voter, option as usize)
            .map_err(|e| JsError::new(&e))
    }

    /// **Cast voter `voter`'s ballot for `option`** — the explicit-ballot cast (the shape a
    /// `<dregg-poll>` uses to bind a cast to the visitor's own ballot). Re-casting the SAME
    /// voter is refused by the nullifier set (the engine double-vote depth).
    #[wasm_bindgen(js_name = castAs)]
    pub fn cast_as(&mut self, voter: usize, option: i32) -> Result<u64, JsError> {
        self.do_cast(voter, option as usize)
            .map_err(|e| JsError::new(&e))
    }

    /// **Prove one-vote-per-ballot BITES at the engine depth** — attempt to re-cast voter
    /// `voter`'s already-consumed ballot for `option`. Returns JSON `{refused, reason}`;
    /// `refused: true` is the witnessed nullifier refusal (the consumed-ballot-proof depth).
    #[wasm_bindgen(js_name = tryDoubleVote)]
    pub fn try_double_vote(&mut self, voter: usize, option: i32) -> String {
        use serde_json::json;
        match self.do_cast(voter, option as usize) {
            Ok(_) => json!({
                "refused": false,
                "reason": "double vote COMMITTED — one-vote-per-ballot did not bite!"
            })
            .to_string(),
            Err(e) => json!({ "refused": true, "reason": e }).to_string(),
        }
    }

    /// **Prove the ballot's `WriteOnce(VOTE)` BITES at the EXECUTOR depth** — attempt a second,
    /// value-CHANGING write to voter `voter`'s already-voted ballot directly over the verified
    /// executor (bypassing the engine nullifier), which the ballot cell's `WriteOnce(VOTE)`
    /// caveat must REFUSE on the commit path. Returns JSON `{refused, reason}`; `refused: true`
    /// is the on-ledger one-vote-per-ballot enforcement (`collective-choice` depth (i)).
    #[wasm_bindgen(js_name = tryBallotWriteOnce)]
    pub fn try_ballot_write_once(&mut self, voter: usize) -> String {
        use serde_json::json;
        let ballot = match self.ballots.get(voter).copied() {
            Some(b) => b,
            None => {
                return json!({ "refused": false, "reason": "voter has no issued ballot yet" })
                    .to_string();
            }
        };
        let current = self
            .rt
            .cell_field(&ballot, BALLOT_VOTE_SLOT)
            .map(|fe| be_to_u64(&fe))
            .unwrap_or(0);
        if current == 0 {
            return json!({ "refused": false, "reason": "ballot has not voted yet — nothing to overwrite" })
                .to_string();
        }
        // A DIFFERENT choice value (current + 1) → the WriteOnce caveat (old set, new != old)
        // must fail. `IncrementNonce` chains the ballot so the transition witnesses the write.
        let effects = vec![
            Effect::SetField {
                cell: ballot,
                index: BALLOT_VOTE_SLOT,
                value: fe_be(current + 1),
            },
            Effect::IncrementNonce { cell: ballot },
        ];
        match self
            .rt
            .execute_app_turn_for_agent(0, ballot, "cast_vote", effects, POLL_FEE)
        {
            Ok(TurnResult::Rejected { reason, .. }) => {
                json!({ "refused": true, "reason": format!("{reason}") }).to_string()
            }
            Ok(TurnResult::Committed { .. }) => json!({
                "refused": false,
                "reason": "overwrite COMMITTED — WriteOnce(VOTE) did not bite!"
            })
            .to_string(),
            Ok(other) => json!({ "refused": false, "reason": format!("{other:?}") }).to_string(),
            Err(e) => json!({ "refused": false, "reason": e }).to_string(),
        }
    }

    /// **Attempt the decision-turn** — set `RESOLVED := 1` on the poll cell, which the polis
    /// quorum `AffineLe` (`M·RESOLVED − Σ TALLY ≤ 0`) admits ONLY once `Σ TALLY ≥ M`. Returns
    /// JSON `{resolved, winner, winner_tally, total, reason}`. Below quorum the executor
    /// refuses the turn (`resolved: false`); at/above quorum it commits. Idempotent once resolved.
    #[wasm_bindgen(js_name = tryResolve)]
    pub fn try_resolve(&mut self) -> String {
        use serde_json::json;
        let already = self
            .rt
            .cell_field(&self.poll, POLL_RESOLVED_SLOT)
            .map(|fe| be_to_u64(&fe))
            .unwrap_or(0)
            != 0;
        if already {
            let (winner, wt) = self.argmax();
            return json!({
                "resolved": true, "winner": winner, "winner_tally": wt,
                "total": self.total(), "reason": "already resolved"
            })
            .to_string();
        }
        let poll = self.poll;
        let effects = vec![
            Effect::SetField {
                cell: poll,
                index: POLL_RESOLVED_SLOT,
                value: fe_be(1),
            },
            Effect::IncrementNonce { cell: poll },
        ];
        match self
            .rt
            .execute_app_turn_for_agent(0, poll, "resolve", effects, POLL_FEE)
        {
            Ok(TurnResult::Committed { .. }) => {
                let (winner, wt) = self.argmax();
                json!({
                    "resolved": true, "winner": winner, "winner_tally": wt,
                    "total": self.total(), "reason": "quorum met — decision-turn committed"
                })
                .to_string()
            }
            Ok(TurnResult::Rejected { reason, .. }) => json!({
                "resolved": false,
                "reason": format!("below quorum — the AffineLe gate refused: {reason}")
            })
            .to_string(),
            Ok(other) => json!({ "resolved": false, "reason": format!("{other:?}") }).to_string(),
            Err(e) => json!({ "resolved": false, "reason": e }).to_string(),
        }
    }

    /// **THE POLL VIEW-TREE** — a titled column over a `table` of option rows, each
    /// `row(text(label), bind(tally slot))`. The SAME `{kind, props, children}` JSON the web
    /// renderer (`deos-view::parse_view_tree`) consumes — serve it and the live board paints.
    #[wasm_bindgen(js_name = viewTreeJson)]
    pub fn view_tree_json(&self) -> String {
        use serde_json::json;
        let mut rows: Vec<serde_json::Value> = Vec::new();
        for i in 0..self.option_count {
            rows.push(json!({
                "kind": "row",
                "props": {},
                "children": [
                    { "kind": "text", "props": { "text": format!("option {i}: ") } },
                    { "kind": "bind", "props": { "slot": POLL_TALLY_BASE + i, "label": "" } }
                ]
            }));
        }
        json!({
            "kind": "vstack",
            "props": {},
            "children": [
                { "kind": "text", "props": { "text": format!("Collective choice — {} options · quorum {}", self.option_count, self.quorum_m) } },
                { "kind": "table", "props": {}, "children": rows }
            ]
        })
        .to_string()
    }

    /// **RENDER THE LIVE TALLY TO HTML, IN-WASM** — [`Self::view_tree_json`] walked through the
    /// gpui-free web renderer, each option's live `bind` painted from its `Monotonic` tally slot
    /// off the committed poll cell. The `<dregg-poll>` Custom Element repaints via this after
    /// each `cast`.
    #[wasm_bindgen(js_name = renderHtml)]
    pub fn render_html(&self) -> String {
        render_world_html(&self.view_tree_json(), |slot| {
            self.rt
                .cell_field(&self.poll, slot)
                .map(|fe| be_to_u64(&fe))
                .unwrap_or(0)
        })
    }

    // ── internals ───────────────────────────────────────────────────────────────────────

    /// Light-client counts from the append-only cast log alone (no executor slot read).
    fn light_client_counts(&self) -> Vec<u64> {
        let mut per = vec![0u64; self.option_count];
        for &opt in &self.cast_log {
            if opt < per.len() {
                per[opt] += 1;
            }
        }
        per
    }

    /// Argmax over the live per-option tallies; ties break to the lowest index (mirrors
    /// `collective_choice::argmax`).
    fn argmax(&self) -> (usize, u64) {
        let mut best = 0usize;
        let mut best_v = 0u64;
        for i in 0..self.option_count {
            let v = self.read(i);
            if v > best_v {
                best = i;
                best_v = v;
            }
        }
        (best, best_v)
    }

    /// Issue (or return the existing) ballot cell for voter `voter` — a factory-shaped cell
    /// carrying `WriteOnce(VOTE)`, with the operator granted a reach cap so the cast turn can
    /// author against it. Deterministic per voter (one ballot per voter), so a re-issue is a
    /// no-op — the single-use-cap depth of one-vote-per-ballot.
    fn issue_ballot(&mut self, voter: usize) -> Result<dregg_types::CellId, String> {
        while self.ballots.len() <= voter {
            let idx = self.ballots.len();
            let owner = Self::voter_pk(idx);
            let ballot = self.rt.mint_cell_from_genesis(owner, 0)?;
            self.rt.install_app_program(
                &ballot,
                Self::ballot_program(),
                dregg_cell::CellState::new(0),
            )?;
            self.rt.grant_reach_capability(0, ballot)?;
            self.ballots.push(ballot);
        }
        Ok(self.ballots[voter])
    }

    /// The real cast: (iii) refuse a consumed nullifier, (i) write the ballot's `WriteOnce(VOTE)`
    /// as a verified turn, then (ii) bump the poll's `Monotonic` tally as a verified turn, and
    /// record the cast for the light client. Two genuine cap-gated verified turns per vote.
    fn do_cast(&mut self, voter: usize, option: usize) -> Result<u64, String> {
        if option >= self.option_count {
            return Err(format!(
                "option {option} out of range (0..{})",
                self.option_count
            ));
        }
        let ballot = self.issue_ballot(voter)?;

        // Depth (iii): the nullifier set — a consumed ballot proof is refused engine-wide.
        let nullifier = *blake3::hash(&[&self.poll.0[..], &ballot.0[..]].concat()).as_bytes();
        if self.nullifiers.contains(&nullifier) {
            return Err("ballot nullifier already consumed (double vote)".to_string());
        }

        // Depth (i): the ballot's `WriteOnce(VOTE)` — the choice code is `option + 1` (non-zero
        // so WriteOnce treats it as "set"). A real cap-gated verified turn → a receipt.
        let choice = option as u64 + 1;
        let ballot_effects = vec![
            Effect::SetField {
                cell: ballot,
                index: BALLOT_VOTE_SLOT,
                value: fe_be(choice),
            },
            Effect::IncrementNonce { cell: ballot },
        ];
        match self
            .rt
            .execute_app_turn_for_agent(0, ballot, "cast_vote", ballot_effects, POLL_FEE)
        {
            Ok(TurnResult::Committed { .. }) => {}
            Ok(TurnResult::Rejected { reason, at_action }) => {
                return Err(format!("ballot turn refused: {reason} (at {at_action:?})"));
            }
            Ok(other) => return Err(format!("ballot turn not committed: {other:?}")),
            Err(e) => return Err(e),
        }
        self.nullifiers.insert(nullifier);

        // Depth (ii): the poll's `Monotonic` tally bump — read the live slot, write `live + 1`.
        // A stale value cannot shrink the board (the executor re-enforces Monotonic).
        let live = self.read(option);
        let poll = self.poll;
        let tally_effects = vec![
            Effect::SetField {
                cell: poll,
                index: POLL_TALLY_BASE + option,
                value: fe_be(live + 1),
            },
            Effect::IncrementNonce { cell: poll },
        ];
        match self
            .rt
            .execute_app_turn_for_agent(0, poll, "record_tally", tally_effects, POLL_FEE)
        {
            Ok(TurnResult::Committed { .. }) => {}
            Ok(TurnResult::Rejected { reason, at_action }) => {
                return Err(format!("tally turn refused: {reason} (at {at_action:?})"));
            }
            Ok(other) => return Err(format!("tally turn not committed: {other:?}")),
            Err(e) => return Err(e),
        }

        self.cast_log.push(option);
        Ok(self.read(option))
    }

    /// The deterministic per-voter owner key: `blake3("pollworld-voter" ‖ i)`. Distinct per
    /// voter, so each voter's ballot is a distinct cell (the per-voter blinding-token model).
    fn voter_pk(i: usize) -> [u8; 32] {
        *blake3::hash(
            &[
                b"dregg-wasm-pollworld-voter".as_slice(),
                &(i as u64).to_le_bytes(),
            ]
            .concat(),
        )
        .as_bytes()
    }

    /// The ballot cell's program — `WriteOnce(VOTE)`: the vote slot admits one non-zero write,
    /// frozen thereafter (mirrors `starbridge_privacy_voting`'s ballot `WriteOnce(VOTE)` caveat).
    fn ballot_program() -> dregg_cell::CellProgram {
        use dregg_cell::program::StateConstraint;
        dregg_cell::CellProgram::always(vec![StateConstraint::WriteOnce {
            index: BALLOT_VOTE_SLOT as u8,
        }])
    }

    /// The poll (tally-board) cell's program — the three executor-enforced teeth (mirrors
    /// `collective_choice::CollectiveChoice::poll_program`): `Monotonic` on every tally slot,
    /// `WriteOnce(RESOLVED)`, and the polis quorum `AffineLe { M·RESOLVED − Σ TALLY_i ≤ 0 }`.
    fn poll_program(quorum_m: u64, option_count: usize) -> dregg_cell::CellProgram {
        use dregg_cell::program::StateConstraint;
        let mut cs: Vec<StateConstraint> = Vec::new();
        for i in 0..POLL_MAX_OPTIONS {
            cs.push(StateConstraint::Monotonic {
                index: (POLL_TALLY_BASE + i) as u8,
            });
        }
        cs.push(StateConstraint::WriteOnce {
            index: POLL_RESOLVED_SLOT as u8,
        });
        // THE QUORUM GATE: `M·RESOLVED − Σ TALLY_i ≤ 0`. RESOLVED == 0 ⇒ `−Σ TALLY ≤ 0`
        // (always true); arming RESOLVED := 1 DEMANDS `Σ TALLY ≥ M` in the same post-state.
        let mut terms: Vec<(i64, u8)> = vec![(quorum_m as i64, POLL_RESOLVED_SLOT as u8)];
        for i in 0..option_count {
            terms.push((-1, (POLL_TALLY_BASE + i) as u8));
        }
        cs.push(StateConstraint::AffineLe { terms, c: 0 });
        dregg_cell::CellProgram::always(cs)
    }

    /// The poll cell's genesis state — quorum `M` + option count pinned, all tallies + the
    /// decision flag zeroed (mirrors `collective_choice`'s `seed_poll` genesis).
    fn poll_initial_state(quorum_m: u64, option_count: usize) -> dregg_cell::CellState {
        let mut state = dregg_cell::CellState::new(0);
        state.fields[POLL_QUORUM_M_SLOT] = fe_be(quorum_m);
        state.fields[POLL_OPTION_COUNT_SLOT] = fe_be(option_count as u64);
        state.fields[POLL_RESOLVED_SLOT] = fe_be(0);
        for i in 0..POLL_MAX_OPTIONS {
            state.fields[POLL_TALLY_BASE + i] = fe_be(0);
        }
        state
    }
}
