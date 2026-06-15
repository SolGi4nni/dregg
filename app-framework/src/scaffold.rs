//! `dregg new deos-app` — the **scaffold** for a useful deos app in an afternoon.
//!
//! `docs/deos/DEOS-APPS.md` (§7, the gap): "No builder dev-experience. No `dregg new
//! deos-app` scaffold, no affordance hot-loop, no 'useful deos app in an afternoon.'
//! Adoption (the pug-handoff bar) needs it." This module IS that scaffold: a
//! generator that, from an [`AppSpec`] (the app name + its cells + their
//! affordances), emits a COMPLETE, BUILDABLE deos app — `Cargo.toml`, `src/lib.rs`
//! (the affordances + the composed `register`/`mount`), `src/main.rs` (the
//! one-command serve), and the web-component surface — onto the [`crate::deos_app`]
//! composition.
//!
//! The builder writes the SPEC (what cells, what affordances, what rights, what
//! effects); the framework wires the verified state, the SDK surface, the
//! distribution, the rehydration, and the web surface. That is the deos app model's
//! promise: "the app builder writes *affordances + a surface*; the framework wires
//! the rest."
//!
//! ## Two ways in
//!
//! 1. **In-process (the template module).** Build a [`DeosApp`] directly from an
//!    [`AppSpec`] with [`AppSpec::into_app`] — no codegen, no new crate. This is the
//!    fast loop: declare a spec, get a mounted app. The
//!    [`crate::deos_app::DeosApp`] tests + the re-expressed apps use this.
//! 2. **The generator (`dregg new deos-app`).** Render the spec to a full crate's
//!    source with [`Scaffold::render`] and write it to a directory with
//!    [`Scaffold::write_to`]. This is the "new crate from a one-command path" the
//!    pug-handoff bar needs — the emitted crate builds against `dregg-app-framework`
//!    and serves immediately.
//!
//! ## The one-command path
//!
//! ```ignore
//! // The CLI-shaped entry (a `dregg new deos-app <name>` would call this):
//! let spec = AppSpec::new("guestbook")
//!     .cell(CellSpec::new("book")
//!         .affordance(AffordanceSpec::view("read",  "Signature"))
//!         .affordance(AffordanceSpec::emit("sign",  "Either", "signed"))
//!         .publish("Signature"))
//!     .discoverable(vec!["social".into()]);
//! Scaffold::new(spec).write_to("./guestbook")?; // emits Cargo.toml + src/* + the web surface
//! // then: cd guestbook && cargo run   → a live deos app
//! ```

use std::path::Path;

use dregg_cell::AuthRequired;
use dregg_turn::action::{Effect, Event};
use dregg_types::CellId;

use crate::affordance::CellAffordance;
use crate::cipherclerk::{AppCipherclerk, EmbeddedExecutor};
use crate::deos_app::{DeosApp, DeosCell};

// =============================================================================
// The spec — what the builder writes
// =============================================================================

/// One **affordance** in an [`AppSpec`] — a name, the rights tier a viewer must
/// hold, and the effect kind it fires. The builder declares these; the framework
/// turns each into a real [`CellAffordance`] carrying a genuine [`Effect`].
#[derive(Clone, Debug)]
pub struct AffordanceSpec {
    /// The affordance name (the deos analogue of `hx-post="/comment"`).
    pub name: String,
    /// The rights tier a viewer must HOLD (a label: `none`/`root`, `either`,
    /// `signature`/`sig`, `proof`). Resolved to a real [`AuthRequired`].
    pub required_rights: String,
    /// The effect this affordance fires (the verified turn the executor runs).
    pub effect: AffordanceEffect,
}

/// The effect an [`AffordanceSpec`] fires, in spec form — resolved to a real
/// [`Effect`] against the cell at build time. Kept deliberately small (the common
/// deos shapes); an app that needs an exotic effect drops to a raw [`CellAffordance`].
#[derive(Clone, Debug)]
pub enum AffordanceEffect {
    /// Emit an event on the cell (a view/comment/log) — `Effect::EmitEvent` with the
    /// given topic label (hashed to the 32-byte topic).
    Emit { topic: String },
    /// Write the cell's field at `index` (an edit) — `Effect::SetField`.
    SetField { index: usize },
}

impl AffordanceSpec {
    /// A **view/log** affordance (fires `EmitEvent` with topic = the affordance name).
    pub fn view(name: impl Into<String>, rights: impl Into<String>) -> Self {
        let name = name.into();
        AffordanceSpec {
            required_rights: rights.into(),
            effect: AffordanceEffect::Emit {
                topic: name.clone(),
            },
            name,
        }
    }

    /// An **emit** affordance with an explicit topic label.
    pub fn emit(
        name: impl Into<String>,
        rights: impl Into<String>,
        topic: impl Into<String>,
    ) -> Self {
        AffordanceSpec {
            name: name.into(),
            required_rights: rights.into(),
            effect: AffordanceEffect::Emit {
                topic: topic.into(),
            },
        }
    }

    /// An **edit** affordance that writes field `index` (`SetField`).
    pub fn edit(name: impl Into<String>, rights: impl Into<String>, index: usize) -> Self {
        AffordanceSpec {
            name: name.into(),
            required_rights: rights.into(),
            effect: AffordanceEffect::SetField { index },
        }
    }

    /// Build the real [`CellAffordance`] for this spec against `cell`.
    fn into_affordance(self, cell: CellId) -> Result<CellAffordance, ScaffoldError> {
        let rights = parse_rights(&self.required_rights)
            .ok_or_else(|| ScaffoldError::UnknownRights(self.required_rights.clone()))?;
        let effect = match self.effect {
            AffordanceEffect::Emit { topic } => Effect::EmitEvent {
                cell,
                event: Event {
                    topic: topic_hash(&topic),
                    data: vec![],
                },
            },
            AffordanceEffect::SetField { index } => Effect::SetField {
                cell,
                index,
                value: [0u8; 32],
            },
        };
        Ok(CellAffordance::new(self.name, rights, effect))
    }
}

/// One **cell** in an [`AppSpec`] — its name, its affordances, and whether it is
/// published into the web-of-cells.
#[derive(Clone, Debug)]
pub struct CellSpec {
    /// The cell's surface name (also its route prefix `/{name}`).
    pub name: String,
    /// The affordances this cell exposes.
    pub affordances: Vec<AffordanceSpec>,
    /// If `Some(rights_label)`, the cell is published into the web-of-cells at that
    /// authority (a sturdyref bearer obtains it on enliven).
    pub publish_at: Option<String>,
}

impl CellSpec {
    /// A cell named `name` with no affordances yet.
    pub fn new(name: impl Into<String>) -> Self {
        CellSpec {
            name: name.into(),
            affordances: Vec::new(),
            publish_at: None,
        }
    }

    /// Add an affordance.
    pub fn affordance(mut self, affordance: AffordanceSpec) -> Self {
        self.affordances.push(affordance);
        self
    }

    /// Publish this cell into the web-of-cells at `rights` (a label).
    pub fn publish(mut self, rights: impl Into<String>) -> Self {
        self.publish_at = Some(rights.into());
        self
    }

    /// Build the real [`DeosCell`] for this spec against `cell`.
    fn into_cell(self, cell: CellId) -> Result<DeosCell, ScaffoldError> {
        let mut deos_cell = DeosCell::new(cell, self.name);
        for aff in self.affordances {
            deos_cell = deos_cell.affordance(aff.into_affordance(cell)?);
        }
        if let Some(label) = self.publish_at {
            let rights =
                parse_rights(&label).ok_or_else(|| ScaffoldError::UnknownRights(label.clone()))?;
            deos_cell = deos_cell.publish(rights);
        }
        Ok(deos_cell)
    }
}

/// The **app spec** the builder writes — the app name + its cells + discovery tags.
/// The whole deos app, declaratively. Turn it into a live [`DeosApp`] with
/// [`AppSpec::into_app`], or render a full crate with [`Scaffold`].
#[derive(Clone, Debug)]
pub struct AppSpec {
    /// The app name (the crate name + the manifest's `app` + the nameservice name).
    pub name: String,
    /// The cells this app composes.
    pub cells: Vec<CellSpec>,
    /// If `Some(tags)`, the app is discoverable in the nameservice under these tags.
    pub discovery_tags: Option<Vec<String>>,
}

impl AppSpec {
    /// A spec for an app named `name` with no cells yet.
    pub fn new(name: impl Into<String>) -> Self {
        AppSpec {
            name: name.into(),
            cells: Vec::new(),
            discovery_tags: None,
        }
    }

    /// Add a cell.
    pub fn cell(mut self, cell: CellSpec) -> Self {
        self.cells.push(cell);
        self
    }

    /// Make the app discoverable in the nameservice under `tags`.
    pub fn discoverable(mut self, tags: Vec<String>) -> Self {
        self.discovery_tags = Some(tags);
        self
    }

    /// Build a live [`DeosApp`] from this spec, driven by `cipherclerk` + `executor`.
    ///
    /// Each cell is backed by a DERIVED cell id (`derive_raw(cipherclerk.cell, cell
    /// name)`) so multiple cells in one app are distinct AND deterministic — EXCEPT a
    /// cell named `"self"` (or the FIRST cell when only one) is backed by the
    /// cipherclerk's OWN cell, so its fires execute against the embedded ledger
    /// out-of-the-box (the agent's cell is seeded). This is the in-process template
    /// path — no codegen.
    pub fn into_app(
        self,
        cipherclerk: AppCipherclerk,
        executor: EmbeddedExecutor,
    ) -> Result<DeosApp, ScaffoldError> {
        if self.cells.is_empty() {
            return Err(ScaffoldError::NoCells);
        }
        let own = cipherclerk.cell_id();
        let single = self.cells.len() == 1;
        let mut builder = DeosApp::builder(self.name.clone(), cipherclerk.clone(), executor);
        if let Some(tags) = self.discovery_tags.clone() {
            builder = builder.discoverable(tags);
        }
        for (i, cell_spec) in self.cells.into_iter().enumerate() {
            // The agent's own cell backs `self`, or the sole/first cell (so it
            // executes against the seeded embedded ledger by default).
            let backing = if cell_spec.name == "self" || (single && i == 0) {
                own
            } else {
                CellId::derive_raw(own.as_bytes(), &topic_hash(&cell_spec.name))
            };
            builder = builder.cell(cell_spec.into_cell(backing)?);
        }
        Ok(builder.build())
    }
}

// =============================================================================
// The generator — `dregg new deos-app`
// =============================================================================

/// The **scaffold generator** — renders an [`AppSpec`] to a complete deos-app crate's
/// source (Cargo.toml + src/lib.rs + src/main.rs + the web surface), the
/// `dregg new deos-app` one-command path.
pub struct Scaffold {
    spec: AppSpec,
}

/// The rendered source files of a scaffolded deos-app crate — relative path → content.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScaffoldFiles {
    /// `Cargo.toml` — the crate manifest depending on `dregg-app-framework`.
    pub cargo_toml: String,
    /// `src/lib.rs` — the affordances + the composed `build_app(cipherclerk, executor)`.
    pub lib_rs: String,
    /// `src/main.rs` — the one-command serve (build the app, mount, serve).
    pub main_rs: String,
    /// `web/<app>.surface.js` — the generated web-component surface (the htmx-on-crack
    /// custom element + the anti-drift affordance constants the page renders from).
    pub surface_js: String,
    /// `README.md` — the one-command path + the affordance map.
    pub readme: String,
}

impl Scaffold {
    /// A scaffold for `spec`.
    pub fn new(spec: AppSpec) -> Self {
        Scaffold { spec }
    }

    /// Render the crate's source files WITHOUT writing them (so a caller can inspect /
    /// test them). Fails only if the spec's rights labels are unparseable.
    pub fn render(&self) -> Result<ScaffoldFiles, ScaffoldError> {
        // Validate the spec by building it against a throwaway agent — surfaces bad
        // rights labels / empty cells BEFORE emitting half a crate.
        let probe_cclerk = AppCipherclerk::new(dregg_sdk::AgentCipherclerk::new(), [0u8; 32]);
        let probe_exec = EmbeddedExecutor::new(&probe_cclerk, "default");
        let app = self.spec.clone().into_app(probe_cclerk, probe_exec)?;

        Ok(ScaffoldFiles {
            cargo_toml: self.render_cargo_toml(),
            lib_rs: self.render_lib_rs(),
            main_rs: self.render_main_rs(),
            surface_js: crate::webgen::render_surface_component(&app),
            readme: self.render_readme(),
        })
    }

    /// Render the crate to `dir` (creating it + `src/` + `web/`). The emitted crate
    /// builds against `dregg-app-framework` and serves immediately:
    /// `cd <dir> && cargo run`.
    pub fn write_to(&self, dir: impl AsRef<Path>) -> Result<(), ScaffoldError> {
        let dir = dir.as_ref();
        let files = self.render()?;
        std::fs::create_dir_all(dir.join("src"))?;
        std::fs::create_dir_all(dir.join("web"))?;
        std::fs::write(dir.join("Cargo.toml"), files.cargo_toml)?;
        std::fs::write(dir.join("src/lib.rs"), files.lib_rs)?;
        std::fs::write(dir.join("src/main.rs"), files.main_rs)?;
        std::fs::write(
            dir.join(format!("web/{}.surface.js", self.spec.name)),
            files.surface_js,
        )?;
        std::fs::write(dir.join("README.md"), files.readme)?;
        Ok(())
    }

    fn render_cargo_toml(&self) -> String {
        format!(
            "# AUTOGENERATED by `dregg new deos-app` — a composed deos app.\n\
             [package]\n\
             name = \"{name}\"\n\
             version = \"0.1.0\"\n\
             edition = \"2021\"\n\
             \n\
             [dependencies]\n\
             dregg-app-framework = {{ path = \"../app-framework\" }}\n\
             tokio = {{ version = \"1\", features = [\"full\"] }}\n",
            name = self.spec.name
        )
    }

    fn render_lib_rs(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!(
            "//! `{name}` — a composed deos app (AUTOGENERATED by `dregg new deos-app`).\n\
             //!\n\
             //! The builder wrote the affordances; the framework wires the verified state,\n\
             //! the SDK surface, the web-of-cells distribution, the rehydration, and the web\n\
             //! surface (`web/{name}.surface.js`). See `docs/deos/DEOS-APPS.md`.\n\n\
             use dregg_app_framework::deos_app::DeosApp;\n\
             use dregg_app_framework::scaffold::{{AffordanceSpec, AppSpec, CellSpec}};\n\
             use dregg_app_framework::{{AppCipherclerk, EmbeddedExecutor}};\n\n\
             /// The app's declarative spec — the single source of truth the affordances,\n\
             /// the web surface, and the manifest are all derived from.\n\
             pub fn spec() -> AppSpec {{\n",
            name = self.spec.name
        ));
        s.push_str(&format!("    AppSpec::new(\"{}\")\n", self.spec.name));
        for cell in &self.spec.cells {
            s.push_str(&format!(
                "        .cell(\n            CellSpec::new(\"{}\")\n",
                cell.name
            ));
            for aff in &cell.affordances {
                match &aff.effect {
                    AffordanceEffect::Emit { topic } => s.push_str(&format!(
                        "                .affordance(AffordanceSpec::emit(\"{}\", \"{}\", \"{}\"))\n",
                        aff.name, aff.required_rights, topic
                    )),
                    AffordanceEffect::SetField { index } => s.push_str(&format!(
                        "                .affordance(AffordanceSpec::edit(\"{}\", \"{}\", {}))\n",
                        aff.name, aff.required_rights, index
                    )),
                }
            }
            if let Some(p) = &cell.publish_at {
                s.push_str(&format!("                .publish(\"{p}\")\n"));
            }
            s.push_str("        )\n");
        }
        if let Some(tags) = &self.spec.discovery_tags {
            let list = tags
                .iter()
                .map(|t| format!("\"{t}\".into()"))
                .collect::<Vec<_>>()
                .join(", ");
            s.push_str(&format!("        .discoverable(vec![{list}])\n"));
        }
        s.push_str("}\n\n");
        s.push_str(
            "/// Build the live, composed [`DeosApp`] from the spec.\n\
             pub fn build_app(cipherclerk: AppCipherclerk, executor: EmbeddedExecutor) -> DeosApp {\n    \
             spec()\n        .into_app(cipherclerk, executor)\n        \
             .expect(\"the generated spec is valid by construction\")\n}\n",
        );
        s
    }

    fn render_main_rs(&self) -> String {
        format!(
            "//! `{name}` — one-command serve (AUTOGENERATED by `dregg new deos-app`).\n\
             //!\n\
             //! `cargo run` → a live deos app: the composed affordance surface, served over\n\
             //! HTTP, every fire a real verified turn through the embedded executor.\n\n\
             use dregg_app_framework::server::{{AppConfig, AppServer}};\n\
             use dregg_app_framework::{{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor}};\n\n\
             #[tokio::main]\n\
             async fn main() {{\n    \
             let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0u8; 32]);\n    \
             let executor = EmbeddedExecutor::new(&cipherclerk, \"default\");\n    \
             let app = {name}::build_app(cipherclerk.clone(), executor.clone());\n\n    \
             // ONE mount yields the whole composed surface (the manifest + per-cell\n    \
             // cap-gated affordance fires + the web-of-cells snapshot endpoints).\n    \
             AppServer::new(AppConfig::from_env())\n        \
             .service_name(\"{name}\")\n        \
             .with_health()\n        \
             .with_cors()\n        \
             .with_cipherclerk(cipherclerk)\n        \
             .with_embedded_executor(executor)\n        \
             .routes(app.mount())\n        \
             .serve()\n        \
             .await\n        \
             .unwrap();\n}}\n",
            name = self.spec.name
        )
    }

    fn render_readme(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("# {}\n\n", self.spec.name));
        s.push_str(
            "A composed **deos app** (AUTOGENERATED by `dregg new deos-app`).\n\n\
             ## One command\n\n\
             ```sh\ncargo run\n```\n\n\
             Serves the composed affordance surface over HTTP: the app manifest at\n\
             `GET /manifest`, and per-cell cap-gated affordance fires (each a real\n\
             verified turn through the embedded executor). The web surface\n",
        );
        s.push_str(&format!(
            "(`web/{}.surface.js`) is a generated `<dregg-affordance-surface>` web component.\n\n\
             ## The affordances\n\n",
            self.spec.name
        ));
        for cell in &self.spec.cells {
            s.push_str(&format!("### cell `{}` (`/{}`)\n\n", cell.name, cell.name));
            for aff in &cell.affordances {
                s.push_str(&format!(
                    "- **{}** — requires `{}` → `POST /{}/fire/{}`\n",
                    aff.name, aff.required_rights, cell.name, aff.name
                ));
            }
            s.push('\n');
        }
        s
    }
}

/// What can go wrong scaffolding a deos app from a spec.
#[derive(Debug)]
pub enum ScaffoldError {
    /// A rights label in the spec was not a recognized [`AuthRequired`] tier.
    UnknownRights(String),
    /// The app spec declared no cells.
    NoCells,
    /// An IO error writing the crate.
    Io(std::io::Error),
}

impl std::fmt::Display for ScaffoldError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ScaffoldError::UnknownRights(s) => write!(
                f,
                "unknown rights label `{s}` (expected none/root, either, signature/sig, proof)"
            ),
            ScaffoldError::NoCells => write!(f, "the app spec declared no cells"),
            ScaffoldError::Io(e) => write!(f, "scaffold io error: {e}"),
        }
    }
}

impl std::error::Error for ScaffoldError {}

impl From<std::io::Error> for ScaffoldError {
    fn from(e: std::io::Error) -> Self {
        ScaffoldError::Io(e)
    }
}

/// Parse an [`AuthRequired`] tier from a (case-insensitive) label — the same mapping
/// the affordance endpoint's header resolver uses, shared so a spec and a request
/// speak the same tier vocabulary.
fn parse_rights(label: &str) -> Option<AuthRequired> {
    crate::affordance_endpoint::parse_auth_required(label)
}

/// Hash a topic label to the 32-byte event topic (a deterministic, namespaced
/// derivation so the same label always yields the same topic).
fn topic_hash(label: &str) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-deos-affordance-topic-v1");
    hasher.update(label.as_bytes());
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
        let cclerk = AppCipherclerk::new(dregg_sdk::AgentCipherclerk::new(), [0xCD; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        (cclerk, executor)
    }

    /// A guestbook spec: one cell, two affordances, published + discoverable.
    fn guestbook() -> AppSpec {
        AppSpec::new("guestbook")
            .cell(
                CellSpec::new("book")
                    .affordance(AffordanceSpec::view("read", "signature"))
                    .affordance(AffordanceSpec::emit("sign", "either", "signed"))
                    .affordance(AffordanceSpec::edit("set_title", "none", 0))
                    .publish("signature"),
            )
            .discoverable(vec!["social".into()])
    }

    #[test]
    fn the_spec_builds_a_live_composed_app_in_process() {
        // The fast loop: a spec → a mounted DeosApp, no codegen.
        let (cclerk, executor) = agent();
        let app = guestbook().into_app(cclerk.clone(), executor).unwrap();
        assert_eq!(app.name(), "guestbook");
        assert_eq!(app.cells().len(), 1);
        let cell = &app.cells()[0];
        // The sole cell is backed by the agent's OWN cell (so fires execute).
        assert_eq!(cell.cell(), cclerk.cell_id());
        assert_eq!(
            cell.surface().all_names(),
            vec![
                "read".to_string(),
                "set_title".to_string(),
                "sign".to_string()
            ]
        );
        assert_eq!(cell.published_authority(), Some(&AuthRequired::Signature));
    }

    #[test]
    fn the_affordance_effects_are_real() {
        use crate::affordance::EffectSummary;
        let (cclerk, executor) = agent();
        let app = guestbook().into_app(cclerk.clone(), executor).unwrap();
        let cell = &app.cells()[0];
        let doc = cell.cell();
        // `read`/`sign` are EmitEvent; `set_title` is SetField — the genuine effects.
        assert_eq!(
            cell.surface().get("read").unwrap().effect_summary(),
            EffectSummary::EmitEvent { cell: doc }
        );
        assert_eq!(
            cell.surface().get("set_title").unwrap().effect_summary(),
            EffectSummary::SetField {
                cell: doc,
                index: 0
            }
        );
    }

    #[test]
    fn multiple_cells_get_distinct_backing_ids() {
        let (cclerk, executor) = agent();
        let app = AppSpec::new("multi")
            .cell(CellSpec::new("self").affordance(AffordanceSpec::view("a", "none")))
            .cell(CellSpec::new("other").affordance(AffordanceSpec::view("b", "none")))
            .into_app(cclerk.clone(), executor)
            .unwrap();
        assert_eq!(app.cells().len(), 2);
        // `self` is the agent's own cell; `other` is a distinct derived id.
        assert_eq!(app.cells()[0].cell(), cclerk.cell_id());
        assert_ne!(app.cells()[1].cell(), cclerk.cell_id());
        assert_ne!(app.cells()[0].cell(), app.cells()[1].cell());
    }

    #[test]
    fn an_unknown_rights_label_is_a_clear_error() {
        let (cclerk, executor) = agent();
        let err = AppSpec::new("bad")
            .cell(CellSpec::new("c").affordance(AffordanceSpec::view("x", "superuser")))
            .into_app(cclerk, executor)
            .unwrap_err();
        match err {
            ScaffoldError::UnknownRights(l) => assert_eq!(l, "superuser"),
            other => panic!("expected UnknownRights, got {other}"),
        }
    }

    #[test]
    fn an_empty_spec_is_rejected() {
        let (cclerk, executor) = agent();
        let err = AppSpec::new("empty")
            .into_app(cclerk, executor)
            .unwrap_err();
        assert!(matches!(err, ScaffoldError::NoCells));
    }

    // ── the generator: `dregg new deos-app` renders a buildable crate ──

    #[test]
    fn the_generator_renders_a_buildable_crate() {
        let files = Scaffold::new(guestbook()).render().unwrap();

        // Cargo.toml depends on the framework.
        assert!(files.cargo_toml.contains("name = \"guestbook\""));
        assert!(files.cargo_toml.contains("dregg-app-framework"));

        // lib.rs reconstructs the spec + the composed build_app.
        assert!(files.lib_rs.contains("pub fn spec() -> AppSpec"));
        assert!(files.lib_rs.contains("AppSpec::new(\"guestbook\")"));
        assert!(files.lib_rs.contains("CellSpec::new(\"book\")"));
        assert!(
            files
                .lib_rs
                .contains("AffordanceSpec::emit(\"sign\", \"either\", \"signed\")")
        );
        assert!(
            files
                .lib_rs
                .contains("AffordanceSpec::edit(\"set_title\", \"none\", 0)")
        );
        assert!(files.lib_rs.contains(".publish(\"signature\")"));
        assert!(
            files
                .lib_rs
                .contains(".discoverable(vec![\"social\".into()])")
        );
        assert!(files.lib_rs.contains("pub fn build_app("));

        // main.rs is the one-command serve through the composed mount().
        assert!(files.main_rs.contains("#[tokio::main]"));
        assert!(files.main_rs.contains("guestbook::build_app"));
        assert!(files.main_rs.contains(".routes(app.mount())"));

        // The web surface is a generated web component.
        assert!(files.surface_js.contains("dregg-affordance-surface"));

        // README documents the one-command path + the affordances.
        assert!(files.readme.contains("cargo run"));
        assert!(files.readme.contains("**read**"));
        assert!(files.readme.contains("POST /book/fire/sign"));
    }

    #[test]
    fn the_generator_round_trips_to_disk() {
        let dir = std::env::temp_dir().join(format!("dregg-scaffold-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        Scaffold::new(guestbook()).write_to(&dir).unwrap();

        assert!(dir.join("Cargo.toml").exists());
        assert!(dir.join("src/lib.rs").exists());
        assert!(dir.join("src/main.rs").exists());
        assert!(dir.join("web/guestbook.surface.js").exists());
        assert!(dir.join("README.md").exists());

        // The rendered lib.rs matches what render() produced (deterministic).
        let on_disk = std::fs::read_to_string(dir.join("src/lib.rs")).unwrap();
        assert_eq!(on_disk, Scaffold::new(guestbook()).render().unwrap().lib_rs);

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn the_generator_rejects_a_bad_spec_before_emitting() {
        // A bad rights label fails render() — no half-crate is written.
        let bad = AppSpec::new("bad")
            .cell(CellSpec::new("c").affordance(AffordanceSpec::view("x", "wizard")));
        assert!(Scaffold::new(bad).render().is_err());
    }
}
