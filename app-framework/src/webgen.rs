//! Canonical JS-constants generation for starbridge-apps — the anti-drift
//! bridge between a Rust `src/lib.rs` (the single source of truth) and its
//! `pages/*.js` web surface.
//!
//! # The drift problem
//!
//! Every starbridge-app pins a fixed slot layout (`pub const FOO_SLOT: u8 =
//! 0;`) and a set of event-topic names in `src/lib.rs`. Its web pages
//! (`pages/turn-builders.js`, `pages/inspectors.js`) historically *hand-copied*
//! those numbers and strings into local `const FOO_SLOT = 0;` declarations.
//! Nothing stopped the two from drifting: bump a slot in Rust, forget the JS,
//! and the page silently reads/writes the wrong field — a class of bug that
//! type-checking can never catch because the boundary is a string/number copy
//! across languages.
//!
//! # The fix
//!
//! An app declares its constants ONCE as a [`ConstantsModule`] (built from its
//! own `pub const`s, so the Rust values are authoritative), then:
//!
//! 1. a tiny generator (an `examples/` bin or a test) renders the module to JS
//!    with [`ConstantsModule::render_js`] and writes
//!    `pages/constants.generated.js`;
//! 2. its web pages `import { FOO_SLOT, TOPICS } from
//!    './constants.generated.js'` instead of re-declaring the values;
//! 3. a drift test calls [`ConstantsModule::assert_matches_file`] (or compares
//!    `render_js()` against the committed file) so CI fails the moment the JS
//!    is regenerated-stale.
//!
//! The generated file is deterministic: the same `ConstantsModule` always
//! renders byte-identical output, so the drift check is a plain string compare.

use std::fmt::Write as _;

/// A named numeric slot constant (`pub const FOO_SLOT: u8 = 3` ⇒
/// `Slot { js_name: "FOO_SLOT", value: 3 }`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slot {
    /// The JS identifier to emit (conventionally the same SCREAMING_SNAKE name
    /// as the Rust `const`).
    pub js_name: &'static str,
    /// The slot index. Sourced from the Rust `const` so it cannot drift.
    pub value: u64,
}

/// A canonical constants module for one starbridge-app: the slot layout, the
/// event-topic vocabulary, and any extra scalar/string values the pages need
/// (e.g. a factory-vk hex).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ConstantsModule {
    /// The app name, used only in the generated banner comment.
    pub app: &'static str,
    /// Slot-index constants, emitted as `export const FOO_SLOT = N;`.
    pub slots: Vec<Slot>,
    /// Event-topic names, emitted as a frozen `TOPICS` object keyed by an
    /// UPPERCASE alias so JS reads `TOPICS.REGISTERED` rather than a magic
    /// string. Each entry is `(js_key, topic_string)`.
    pub topics: Vec<(&'static str, String)>,
    /// Extra string constants (e.g. `("FACTORY_VK_HEX", "ab…")`), emitted as
    /// `export const FACTORY_VK_HEX = "…";`.
    pub strings: Vec<(&'static str, String)>,
    /// Affordance surface descriptors, emitted as a frozen `AFFORDANCES` object
    /// keyed by surface name. Each carries the surface's elements (the cap-gated
    /// affordances) with their required rights + effect kinds + the POST fire
    /// endpoints — the page reads THIS rather than hand-copying endpoint paths +
    /// rights labels, so the affordance UI cannot drift from the Rust declarations
    /// (DEOS-APPS.md §"the deos app model"; same anti-drift discipline as `slots`).
    pub affordance_surfaces: Vec<crate::affordance::SurfaceDescriptor>,
}

impl ConstantsModule {
    /// Start an empty module for `app`.
    pub fn new(app: &'static str) -> Self {
        Self {
            app,
            ..Default::default()
        }
    }

    /// Add a slot constant. `value` should come from the Rust `const` directly
    /// (e.g. `.slot("NAME_HASH_SLOT", NAME_HASH_SLOT as u64)`).
    pub fn slot(mut self, js_name: &'static str, value: u64) -> Self {
        self.slots.push(Slot { js_name, value });
        self
    }

    /// Add an event-topic. `js_key` is the UPPERCASE alias used in JS
    /// (`TOPICS.REGISTERED`); `topic` is the exact `symbol()` string the Rust
    /// side emits.
    pub fn topic(mut self, js_key: &'static str, topic: impl Into<String>) -> Self {
        self.topics.push((js_key, topic.into()));
        self
    }

    /// Add an extra string constant (factory-vk hex, tombstone prefix, …).
    pub fn string(mut self, js_name: &'static str, value: impl Into<String>) -> Self {
        self.strings.push((js_name, value.into()));
        self
    }

    /// Add an **affordance surface descriptor** — the cap-gated verified-turn
    /// affordances a deos cell exposes, rendered for the page from the Rust source
    /// of truth.
    ///
    /// `docs/deos/DEOS-APPS.md`: `webgen` grows from "emit JS constants" to render
    /// the affordance SURFACE. Build the descriptor from the live
    /// [`crate::affordance::AffordanceSurface`] (e.g.
    /// `surface.descriptor("/doc-affordances")`) so the JS knows each affordance's
    /// name, the rights a viewer must hold, the effect kind it fires, and the POST
    /// endpoint that fires it (cap-gated) — WITHOUT the page ever re-declaring those
    /// strings. The emitted `AFFORDANCES.<surface>` object is the anti-drift mirror
    /// of the Rust declarations, the same way `TOPICS` mirrors the `symbol()` calls.
    pub fn affordance_surface(mut self, descriptor: crate::affordance::SurfaceDescriptor) -> Self {
        self.affordance_surfaces.push(descriptor);
        self
    }

    /// Render the canonical, deterministic JS module text.
    ///
    /// The output is stable: identical input always yields byte-identical
    /// output, so a drift test can compare it against the committed file with a
    /// plain `==`.
    pub fn render_js(&self) -> String {
        let mut s = String::new();
        let _ = writeln!(
            s,
            "// AUTOGENERATED — do not edit by hand.\n\
             //\n\
             // Canonical constants for the `{app}` starbridge-app, generated from\n\
             // its Rust `src/lib.rs` (the single source of truth) so the web pages\n\
             // cannot drift from the executor's slot layout / event vocabulary.\n\
             //\n\
             // Regenerate with the app's constants generator; a drift test fails if\n\
             // this file is stale.",
            app = self.app
        );
        s.push('\n');

        if !self.slots.is_empty() {
            let _ = writeln!(
                s,
                "// Slot indices (mirror `pub const *_SLOT` in src/lib.rs)."
            );
            for slot in &self.slots {
                let _ = writeln!(s, "export const {} = {};", slot.js_name, slot.value);
            }
            s.push('\n');
        }

        if !self.strings.is_empty() {
            for (name, value) in &self.strings {
                let _ = writeln!(s, "export const {} = {};", name, js_string(value));
            }
            s.push('\n');
        }

        if !self.topics.is_empty() {
            let _ = writeln!(
                s,
                "// Event-topic names (mirror the `symbol(\"…\")` calls in src/lib.rs)."
            );
            let _ = writeln!(s, "export const TOPICS = Object.freeze({{");
            for (key, topic) in &self.topics {
                let _ = writeln!(s, "  {}: {},", key, js_string(topic));
            }
            let _ = writeln!(s, "}});");
        }

        if !self.affordance_surfaces.is_empty() {
            if !self.topics.is_empty() {
                s.push('\n');
            }
            let _ = writeln!(
                s,
                "// Affordance surfaces (mirror the `AffordanceSurface` declarations in\n\
                 // src/lib.rs). Each element is a cap-gated verified-turn affordance: its\n\
                 // required rights, the effect kind it fires, and the POST endpoint that\n\
                 // fires it. The page renders the buttons from THIS — never re-declaring\n\
                 // the endpoint paths or rights labels (anti-drift)."
            );
            let _ = writeln!(s, "export const AFFORDANCES = Object.freeze({{");
            for desc in &self.affordance_surfaces {
                let _ = writeln!(s, "  {}: Object.freeze({{", js_string(&desc.surface));
                let _ = writeln!(s, "    cell: {},", js_string(&desc.cell_hex));
                let _ = writeln!(s, "    routePrefix: {},", js_string(&desc.route_prefix));
                let _ = writeln!(
                    s,
                    "    projectedEndpoint: {},",
                    js_string(&desc.projected_endpoint)
                );
                let _ = writeln!(s, "    elements: Object.freeze([");
                for el in &desc.elements {
                    let _ = writeln!(s, "      Object.freeze({{");
                    let _ = writeln!(s, "        name: {},", js_string(&el.name));
                    let _ = writeln!(
                        s,
                        "        requiredRights: {},",
                        js_string(&el.required_rights)
                    );
                    let _ = writeln!(s, "        effectKind: {},", js_string(&el.effect_kind));
                    let _ = writeln!(s, "        fireEndpoint: {},", js_string(&el.fire_endpoint));
                    let _ = writeln!(s, "      }}),");
                }
                let _ = writeln!(s, "    ]),");
                let _ = writeln!(s, "  }}),");
            }
            let _ = writeln!(s, "}});");
        }

        s
    }

    /// Assert the committed file at `path` byte-equals [`render_js`]. Use this
    /// in a drift test: if it fails, the JS is stale — regenerate it.
    ///
    /// On mismatch the panic message names the path and shows the first
    /// differing line so the fix is obvious.
    ///
    /// [`render_js`]: Self::render_js
    pub fn assert_matches_file(&self, path: &std::path::Path) {
        let expected = self.render_js();
        let actual = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("constants drift check: cannot read {path:?}: {e}"));
        if actual != expected {
            let first_diff = expected
                .lines()
                .zip(actual.lines())
                .enumerate()
                .find(|(_, (e, a))| e != a)
                .map(|(i, (e, a))| {
                    format!("\n  line {}:\n    expected: {e}\n    actual:   {a}", i + 1)
                })
                .unwrap_or_else(|| "\n  (length differs)".to_string());
            panic!(
                "constants drift: {path:?} is stale vs the Rust source of truth.\n\
                 Regenerate the app's constants.generated.js.{first_diff}"
            );
        }
    }
}

/// Render a Rust string as a double-quoted JS string literal (escaping `\` and
/// `"`). The topic/string values are ASCII identifiers in practice, but escape
/// defensively so the generator is total.
fn js_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

// =============================================================================
// The web-component surface — "htmx on crack" as a real custom element
// =============================================================================

/// Render a [`crate::deos_app::DeosApp`]'s **web surface** — a `<dregg-affordance-surface>`
/// custom element + the anti-drift affordance constants — that the embedded servo
/// web-surface (or any browser) mounts to render the cap-gated affordances as
/// interactive DOM.
///
/// `docs/deos/DEOS.md` (§"htmx on crack"): a cell declares affordances and an
/// interaction is a verified turn — "the button is a cap-gated effect, the fragment
/// is the attested post-state surface, and *who may press it* is decided by held
/// capabilities." This generator emits exactly that as a real web component:
///
/// - **`<dregg-affordance-surface route-prefix="/doc" held="signature">`** — on
///   connect, it FETCHES the per-viewer projection from the live affordance endpoint
///   (`GET {route-prefix}/projected`, carrying the held-rights header), so it renders
///   ONLY the affordances the viewer's caps authorize — **progressive enhancement
///   becomes progressive attenuation, in the DOM**. Two viewers mounting the same
///   element with different `held` see DIFFERENT buttons.
/// - **each affordance → a button** whose click POSTs the cap-gated fire
///   (`POST {route-prefix}/fire/{name}`) — a real verified turn — and renders the
///   returned receipt (the attested post-state). An unauthorized fire is the
///   endpoint's 403 (anti-ghost), surfaced inline.
/// - **`AFFORDANCES`** — the frozen anti-drift constant map (the same one
///   [`ConstantsModule::affordance_surface`] emits) the element reads its cell list +
///   fire endpoints from, so the DOM cannot drift from the Rust affordance
///   declarations.
///
/// The output is deterministic (the runtime body is static; only the per-app
/// `AFFORDANCES` map varies), so it can be committed + drift-checked. The element
/// uses the same `x-dregg-held-rights` header the endpoint's default resolver reads,
/// so it drives the genuine gate end-to-end.
pub fn render_surface_component(app: &crate::deos_app::DeosApp) -> String {
    let module = surface_constants_module(app);
    let mut s = String::new();
    let _ = writeln!(
        s,
        "// AUTOGENERATED — the web surface for the `{app}` deos app (do not edit).\n\
         //\n\
         // A `<dregg-affordance-surface>` custom element: htmx-on-crack as a web\n\
         // component. It fetches the PER-VIEWER affordance projection from the live\n\
         // affordance endpoint (so it renders only what the viewer's caps authorize —\n\
         // progressive enhancement becomes progressive ATTENUATION in the DOM) and\n\
         // posts each cap-gated fire as a real verified turn. The embedded servo\n\
         // web-surface mounts this; any browser can too. See docs/deos/DEOS.md.",
        app = app.name()
    );
    s.push('\n');
    // The anti-drift affordance constants (the cell list + fire endpoints).
    s.push_str(&module.render_js());
    s.push('\n');
    // The static custom-element runtime.
    s.push_str(SURFACE_COMPONENT_RUNTIME);
    s
}

/// Build the [`ConstantsModule`] backing an app's web surface — one
/// affordance-surface descriptor per cell, keyed by the cell's route prefix.
fn surface_constants_module(app: &crate::deos_app::DeosApp) -> ConstantsModule {
    // A leaked &'static str for the module banner (the app name). The app name lives
    // for the process; this generator is a build/dev-time tool, so the small leak is
    // acceptable and keeps `ConstantsModule`'s `&'static str` contract.
    let app_name: &'static str = Box::leak(app.name().to_string().into_boxed_str());
    let mut module = ConstantsModule::new(app_name);
    for cell in app.cells() {
        module = module.affordance_surface(cell.surface().descriptor(cell.route_prefix()));
    }
    module
}

/// The static `<dregg-affordance-surface>` custom-element runtime — the htmx-on-crack
/// web component. Pure DOM + `fetch`; no framework. Reads `AFFORDANCES` (emitted
/// above it) for the cell list + endpoints; drives the genuine cap gate via the
/// `x-dregg-held-rights` header the endpoint resolves.
const SURFACE_COMPONENT_RUNTIME: &str = r#"
// The held-rights header the affordance endpoint's default resolver reads. The
// element carries the viewer's tier here so the SERVER gate (real is_attenuation)
// decides what to render + whether a fire may execute — never the client.
const HELD_RIGHTS_HEADER = "x-dregg-held-rights";

function _esc(s) {
  return String(s ?? "").replace(/[&<>"']/g, (c) => ({
    "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;",
  })[c]);
}

// <dregg-affordance-surface route-prefix="/doc" held="signature">
//
// On connect it asks the live endpoint for the per-viewer projection and renders a
// button per authorized affordance. Clicking a button POSTs the cap-gated fire (a
// real verified turn) and shows the attested receipt. Two viewers with different
// `held` see different buttons — the deos confinement property, in the DOM.
class DreggAffordanceSurface extends HTMLElement {
  static get observedAttributes() { return ["route-prefix", "held"]; }

  connectedCallback() { this.render(); }
  attributeChangedCallback() { if (this.isConnected) this.render(); }

  get routePrefix() { return this.getAttribute("route-prefix") || ""; }
  get held() { return this.getAttribute("held") || ""; }

  async render() {
    const prefix = this.routePrefix;
    if (!prefix) { this.innerHTML = '<em>no route-prefix</em>'; return; }
    this.innerHTML = '<div class="dregg-surface-loading">loading affordances…</div>';
    let projected;
    try {
      const resp = await fetch(`${prefix}/projected`, {
        headers: { [HELD_RIGHTS_HEADER]: this.held },
      });
      if (resp.status === 401) {
        this.innerHTML = '<div class="dregg-surface-denied">no authority presented</div>';
        return;
      }
      projected = await resp.json();
    } catch (e) {
      this.innerHTML = `<div class="dregg-surface-error">${_esc(e.message || e)}</div>`;
      return;
    }
    const elements = (projected && projected.elements) || [];
    const held = _esc((projected && projected.held) || this.held);
    const buttons = elements.map((el) => `
      <button class="dregg-affordance" data-fire="${_esc(el.fireEndpoint)}" data-name="${_esc(el.name)}">
        ${_esc(el.name)}
        <small class="dregg-affordance-meta">${_esc(el.effectKind)} · needs ${_esc(el.requiredRights)}</small>
      </button>`).join("");
    this.innerHTML = `
      <div class="dregg-affordance-surface" data-held="${held}">
        <header class="dregg-surface-head">held: <code>${held}</code></header>
        <div class="dregg-affordance-row">${buttons || '<em>no affordances for this viewer</em>'}</div>
        <output class="dregg-surface-receipt"></output>
      </div>`;
    this.querySelectorAll("button.dregg-affordance").forEach((b) => {
      b.addEventListener("click", () => this.fire(b.dataset.fire, b.dataset.name));
    });
  }

  // Fire a cap-gated affordance: POST the verified turn, render the attested receipt.
  // A 403 (unauthorized) is surfaced inline — the anti-ghost refusal, in the DOM.
  async fire(endpoint, name) {
    const out = this.querySelector("output.dregg-surface-receipt");
    if (out) out.textContent = `firing ${name}…`;
    try {
      const resp = await fetch(endpoint, {
        method: "POST",
        headers: { [HELD_RIGHTS_HEADER]: this.held },
      });
      const body = await resp.json().catch(() => ({}));
      if (resp.status === 403) {
        if (out) out.innerHTML = `<span class="dregg-fire-refused">refused: ${_esc(body.error || "unauthorized")}</span>`;
        return;
      }
      if (!resp.ok) {
        if (out) out.innerHTML = `<span class="dregg-fire-error">error: ${_esc(body.error || resp.status)}</span>`;
        return;
      }
      // The attested post-state: the executor's OWN receipt (turn_hash + post_state).
      if (out) out.innerHTML =
        `<span class="dregg-fire-ok">fired <b>${_esc(body.fired)}</b> — turn ${_esc(String(body.turn_hash).slice(0, 12))}…</span>`;
      this.dispatchEvent(new CustomEvent("dregg-fired", { detail: body, bubbles: true }));
    } catch (e) {
      if (out) out.innerHTML = `<span class="dregg-fire-error">${_esc(e.message || e)}</span>`;
    }
  }
}

if (typeof customElements !== "undefined" && !customElements.get("dregg-affordance-surface")) {
  customElements.define("dregg-affordance-surface", DreggAffordanceSurface);
}

export { DreggAffordanceSurface, AFFORDANCES };
"#;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_is_deterministic_and_well_formed() {
        let m = ConstantsModule::new("nameservice")
            .slot("NAME_HASH_SLOT", 2)
            .slot("OWNER_HASH_SLOT", 3)
            .string("FACTORY_VK_HEX", "abcd")
            .topic("REGISTERED", "name-registered")
            .topic("REVOKED", "name-revoked");

        let a = m.render_js();
        let b = m.render_js();
        assert_eq!(a, b, "render must be deterministic");

        assert!(a.contains("export const NAME_HASH_SLOT = 2;"));
        assert!(a.contains("export const OWNER_HASH_SLOT = 3;"));
        assert!(a.contains("export const FACTORY_VK_HEX = \"abcd\";"));
        assert!(a.contains("REGISTERED: \"name-registered\","));
        assert!(a.contains("REVOKED: \"name-revoked\","));
        assert!(a.contains("Object.freeze("));
    }

    #[test]
    fn js_string_escapes() {
        assert_eq!(js_string("a\"b\\c"), "\"a\\\"b\\\\c\"");
    }

    #[test]
    fn affordance_surface_renders_anti_drift_descriptor() {
        use crate::affordance::{AffordanceSurface, CellAffordance};
        use dregg_cell::AuthRequired;
        use dregg_turn::action::{Effect, Event};

        let doc = dregg_types::CellId::from_bytes([5u8; 32]);
        let surface = AffordanceSurface::named(doc, "doc")
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature,
                Effect::EmitEvent {
                    cell: doc,
                    event: Event {
                        topic: [1u8; 32],
                        data: vec![],
                    },
                },
            ))
            .declare(CellAffordance::new(
                "edit",
                AuthRequired::Either,
                Effect::SetField {
                    cell: doc,
                    index: 1,
                    value: [0u8; 32],
                },
            ));

        let m = ConstantsModule::new("doc-app")
            .slot("DOC_BODY_SLOT", 1)
            .affordance_surface(surface.descriptor("/doc-affordances"));

        let a = m.render_js();
        let b = m.render_js();
        assert_eq!(a, b, "render must be deterministic");

        // The slots still render.
        assert!(a.contains("export const DOC_BODY_SLOT = 1;"));
        // The affordance surface renders as a frozen object the page reads.
        assert!(a.contains("export const AFFORDANCES = Object.freeze("));
        assert!(a.contains("\"doc\": Object.freeze("));
        // Each element carries its required rights, effect kind, and fire endpoint —
        // from the Rust source of truth (anti-drift).
        assert!(a.contains("name: \"view\","));
        assert!(a.contains("requiredRights: \"Signature\","));
        assert!(a.contains("effectKind: \"EmitEvent\","));
        assert!(a.contains("fireEndpoint: \"/doc-affordances/fire/view\","));
        assert!(a.contains("name: \"edit\","));
        assert!(a.contains("requiredRights: \"Either\","));
        assert!(a.contains("effectKind: \"SetField\","));
        assert!(a.contains("fireEndpoint: \"/doc-affordances/fire/edit\","));
        // The projection endpoint is named.
        assert!(a.contains("projectedEndpoint: \"/doc-affordances/projected\","));
    }

    #[test]
    fn assert_matches_file_roundtrips(/* uses a temp file */) {
        let m = ConstantsModule::new("x").slot("FOO_SLOT", 7);
        let dir = std::env::temp_dir();
        let path = dir.join(format!("webgen-test-{}.generated.js", std::process::id()));
        std::fs::write(&path, m.render_js()).unwrap();
        m.assert_matches_file(&path);
        std::fs::remove_file(&path).ok();
    }
}
