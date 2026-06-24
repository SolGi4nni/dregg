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
                self.commit_set(next).map_err(|e| JsError::new(&e.to_string()))?;
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
