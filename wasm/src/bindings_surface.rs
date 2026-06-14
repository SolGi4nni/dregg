//! `#[wasm_bindgen]` entry points for the WEB SURFACE (N10).
//!
//! These mirror `sel4/dregg-firmament/src/surface.rs`'s verbs (`open_surface` /
//! `present` / `share_surface` / `revoke_surface` / `surface_identity`) over the
//! live [`DreggRuntime`](crate::runtime::DreggRuntime) ledger+executor. They are
//! the smallest change that makes "a browser surface = a cell's surface cap"
//! callable from JS — the same `handle: usize` + `with_runtime`/`with_runtime_ref`
//! shape as the ~80 bindings already in `bindings.rs`.
//!
//! `rights` strings speak the REAL dregg `AuthRequired` lattice (`none`,
//! `signature`/`read-only`, `proof`, `either`/`writable`, `impossible`), NOT a
//! parallel read/write enum — so the over-share refusal is the genuine
//! `granted ⊆ held` direction the executor enforces.

use wasm_bindgen::prelude::*;

// Reuse the runtime store + accessors defined in `bindings`.
use crate::bindings::{with_runtime, with_runtime_ref};

/// **OPEN-SURFACE** — open the `owner_agent_index` agent's OWN cell as a surface
/// (a window) at `rights`, and return its live identity (the T2 badge source).
///
/// A surface IS a cell; this confirms the cell exists, hands the owner an
/// ORIGINAL self-cap over it at `rights` (the Viewport the compositor renders),
/// and reads off the live identity. Returns the `SurfaceIdentity`
/// `{ owning_cell_id, lifecycle, source_state_root, balance, accepts_effects }`
/// drawn FROM THE LEDGER — so the JS compositor draws the badge from the live
/// cell, never the page.
#[wasm_bindgen]
pub fn open_surface(
    handle: usize,
    owner_agent_index: usize,
    rights: &str,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        let id = rt.open_surface(owner_agent_index, rights)?;
        serde_wasm_bindgen::to_value(&id).map_err(|e| e.to_string())
    })
}

/// **PRESENT** — does `holder_agent_index` hold draw authority (`required`) over
/// the surface backed by `surface_owner_agent_index`'s cell?
///
/// Resolves the surface cap against real cell-state requiring `required`
/// (`required ⊆ held`, the REAL `is_attenuation`). A read-only mirror asking for
/// a wider authority is refused. Returns a `SurfaceOutcome`
/// `{ ok, reason, revocation_immediate, commit_synchronous }`; on refusal
/// `reason` is the teaching string. (For the owner presenting into its own
/// window, pass the same index for holder and surface owner.)
#[wasm_bindgen]
pub fn present_surface(
    handle: usize,
    holder_agent_index: usize,
    surface_owner_agent_index: usize,
    required: &str,
) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let outcome =
            rt.present_surface(holder_agent_index, surface_owner_agent_index, required)?;
        serde_wasm_bindgen::to_value(&outcome).map_err(|e| e.to_string())
    })
}

/// **SHARE-SURFACE** — hand the window backed by `surface_owner_agent_index`'s
/// cell from `from_agent_index` to `to_agent_index`, narrowed to `narrower`, as a
/// GENUINE `Effect::GrantCapability` turn through the real executor.
///
/// The executor enforces `granted ⊆ held`: an attenuating share commits; a
/// WIDENING share is rejected with `DelegationDenied` (the `⚠ over-share` moment
/// at the pixel layer). Returns a `SurfaceOutcome` whose `reason` carries the
/// executor's own reason on refusal.
#[wasm_bindgen]
pub fn share_surface(
    handle: usize,
    from_agent_index: usize,
    to_agent_index: usize,
    surface_owner_agent_index: usize,
    narrower: &str,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        let outcome = rt.share_surface(
            from_agent_index,
            to_agent_index,
            surface_owner_agent_index,
            narrower,
        )?;
        serde_wasm_bindgen::to_value(&outcome).map_err(|e| e.to_string())
    })
}

/// **REVOKE-SURFACE** — drop `holder_agent_index`'s cap over the surface backed
/// by `surface_owner_agent_index`'s cell; the glass goes dark.
///
/// At n=1 (the local tab) this is SYNCHRONOUS — the cap is dead the instant it
/// returns, and a subsequent `present_surface` finds nothing held. Returns
/// `true` iff a live surface cap was removed.
#[wasm_bindgen]
pub fn revoke_surface(
    handle: usize,
    holder_agent_index: usize,
    surface_owner_agent_index: usize,
) -> Result<bool, JsError> {
    with_runtime(handle, |rt| {
        rt.revoke_surface(holder_agent_index, surface_owner_agent_index)
    })
}

/// **SURFACE-IDENTITY** — the anti-spoof T2 badge for the surface backed by
/// `surface_owner_agent_index`'s cell, read FROM THE LIVE LEDGER.
///
/// Returns `{ owning_cell_id, lifecycle, source_state_root, balance,
/// accepts_effects }` — each a function of the cell's real state, never the
/// page's self-description.
#[wasm_bindgen]
pub fn surface_identity(
    handle: usize,
    surface_owner_agent_index: usize,
) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let id = rt.surface_identity(surface_owner_agent_index)?;
        serde_wasm_bindgen::to_value(&id).map_err(|e| e.to_string())
    })
}

/// Does `holder_agent_index` hold a surface cap over the surface backed by
/// `surface_owner_agent_index`'s cell? (Used by the compositor to decide whether
/// to paint a recipient's pane.)
#[wasm_bindgen]
pub fn surface_holds_cap(
    handle: usize,
    holder_agent_index: usize,
    surface_owner_agent_index: usize,
) -> Result<bool, JsError> {
    with_runtime_ref(handle, |rt| {
        rt.surface_holds_cap(holder_agent_index, surface_owner_agent_index)
    })
}

/// The rights `holder_agent_index` holds over the surface backed by
/// `surface_owner_agent_index`'s cell, as a string (e.g. `"Signature"`,
/// `"None"`), or `null` if none. (The compositor renders the pane's CAN/CAN'T
/// chrome from this.)
#[wasm_bindgen]
pub fn surface_rights_held(
    handle: usize,
    holder_agent_index: usize,
    surface_owner_agent_index: usize,
) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let held = rt.surface_rights_held(holder_agent_index, surface_owner_agent_index)?;
        serde_wasm_bindgen::to_value(&held).map_err(|e| e.to_string())
    })
}
