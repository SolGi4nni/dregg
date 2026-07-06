//! `source_health` — the console's **source-honesty layer**: where the dashboard's
//! data came from and whether the source answered, so a face can always tell the
//! viewer what they are looking at.
//!
//! Ported dregg-native from the prior operated layer (`SourceHealth`,
//! model.rs:229-301) — the epistemics the retired console enforced, now carried by
//! the native console card (see WIRED below):
//!
//! * **unreachable ≠ empty** — a source that did not answer must render as
//!   "can't reach", NEVER as an empty account with get-started CTAs;
//! * **demo/fixture data is labeled** — baked demo data renders with a banner,
//!   never passed off as a live read;
//! * **unconfigured ≠ broken** — no source configured at all is a calm
//!   "not connected" notice, with the resource panels absent entirely (no false
//!   empty states);
//! * **partial reads are partial** — a surface that failed renders a load error
//!   in its panel while the surfaces that answered render their data;
//! * **not-served is an honest empty** — a surface the source answers "not
//!   found" for (it does not serve it yet) may render an empty panel honestly.
//!
//! This module is the pure model (std + serde only, like the rest of the
//! `dumb-views` floor). Faces consume [`SourceHealth::banner`] for the page-level
//! notice and [`SourceHealth::surface_note`] per panel; `panels_renderable`
//! decides whether resource panels appear at all.
//!
//! WIRED: `console::ConsoleModel` carries a `health: SourceHealth` field (default
//! healthy-live); `console_card` renders the [`Banner`] page-level, gates the
//! resource panels on [`SourceHealth::panels_renderable`], and paints each panel's
//! [`SurfaceNote`]; the cap-scoped catalog reports health through
//! `catalog::Catalog::health` and `ConsoleModel::from_catalog` carries it through.

use serde::{Deserialize, Serialize};

/// Where a console view's data came from and whether the source answered —
/// rendered as the page banner so a viewer always knows what they are looking at.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct SourceHealth {
    /// `"live"` (real cell/world reads) or `"demo"` (baked demo data).
    pub source: String,
    /// Whether a live source is configured at all. `false` → the page shows a
    /// not-connected notice instead of resource panels.
    pub configured: bool,
    /// The configured source endpoint/world label, for the banner/notice text.
    pub endpoint: Option<String>,
    /// Every attempted surface failed to answer — the source is unreachable.
    /// The page shows a can't-reach notice instead of false empty panels.
    pub source_unreachable: bool,
    /// Surfaces that were configured but did not answer (connect/read failure).
    pub unreachable: Vec<String>,
    /// Surfaces the source answered not-found for — it does not serve them yet.
    pub unavailable: Vec<String>,
}

impl Default for SourceHealth {
    /// A healthy live read: configured, reachable, every surface answered.
    fn default() -> Self {
        SourceHealth {
            source: "live".to_string(),
            configured: true,
            endpoint: None,
            source_unreachable: false,
            unreachable: Vec::new(),
            unavailable: Vec::new(),
        }
    }
}

/// The page-level banner a face must render (or the absence of one). Ordered by
/// severity: unconfigured and unreachable displace the panels; demo labels them;
/// partial annotates the affected panels only.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Banner {
    /// Healthy live view — no banner at all.
    None,
    /// No live source is configured; the resource panels are absent entirely.
    NotConnected {
        /// A hint naming what to configure (e.g. an endpoint env/setting name).
        hint: String,
    },
    /// The source is configured but did not answer; this is NOT an empty account.
    Unreachable {
        /// The endpoint that did not answer, if known.
        endpoint: Option<String>,
    },
    /// The view is baked demo data, labeled as such.
    Demo,
    /// Some surfaces answered and render their data; the failed ones carry a
    /// per-panel load error instead of an empty-state CTA.
    Partial {
        /// The surfaces that did not answer.
        failed: Vec<String>,
    },
}

/// What a single surface's panel must show, beyond its data.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SurfaceNote {
    /// The surface answered — render its data (or its honest empty state).
    Ok,
    /// The surface was configured but did not answer — render a load error,
    /// NEVER the get-started empty-state CTA.
    LoadError,
    /// The source does not serve this surface yet — an honest empty is fine.
    NotServed,
}

impl SourceHealth {
    /// The demo/baked source (labeled, never passed off as live).
    pub fn demo() -> Self {
        SourceHealth {
            source: "demo".to_string(),
            ..SourceHealth::default()
        }
    }

    /// A live source with nothing configured.
    pub fn unconfigured() -> Self {
        SourceHealth {
            configured: false,
            ..SourceHealth::default()
        }
    }

    /// Whether the view is demo data.
    pub fn is_demo(&self) -> bool {
        self.source == "demo"
    }

    /// Whether `surface` was configured but did not answer.
    pub fn surface_unreachable(&self, surface: &str) -> bool {
        self.unreachable.iter().any(|s| s == surface)
    }

    /// Whether the source does not serve `surface` (it answered not-found).
    pub fn surface_unavailable(&self, surface: &str) -> bool {
        self.unavailable.iter().any(|s| s == surface)
    }

    /// Whether the resource panels can be rendered meaningfully at all — the
    /// data either came from the demo bake or from a source that answered.
    pub fn panels_renderable(&self) -> bool {
        self.is_demo() || (self.configured && !self.source_unreachable)
    }

    /// The page-level banner for this health state. `hint` names what to
    /// configure in the not-connected notice (an endpoint setting/env name).
    pub fn banner(&self, hint: &str) -> Banner {
        if self.is_demo() {
            return Banner::Demo;
        }
        if !self.configured {
            return Banner::NotConnected {
                hint: hint.to_string(),
            };
        }
        if self.source_unreachable {
            return Banner::Unreachable {
                endpoint: self.endpoint.clone(),
            };
        }
        if !self.unreachable.is_empty() {
            return Banner::Partial {
                failed: self.unreachable.clone(),
            };
        }
        Banner::None
    }

    /// What `surface`'s panel must show beyond its data.
    pub fn surface_note(&self, surface: &str) -> SurfaceNote {
        if self.surface_unreachable(surface) {
            SurfaceNote::LoadError
        } else if self.surface_unavailable(surface) {
            SurfaceNote::NotServed
        } else {
            SurfaceNote::Ok
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── unreachable ≠ empty: the core honesty invariant ───────────────────────
    #[test]
    fn an_unreachable_source_is_never_an_empty_account() {
        let health = SourceHealth {
            endpoint: Some("http://node:8080".into()),
            source_unreachable: true,
            unreachable: vec!["computers".into(), "hermeses".into(), "spend".into()],
            ..SourceHealth::default()
        };
        assert!(!health.panels_renderable(), "no false empty panels");
        assert_eq!(
            health.banner("DEOS_CONSOLE_SOURCE"),
            Banner::Unreachable {
                endpoint: Some("http://node:8080".into())
            }
        );
    }

    #[test]
    fn demo_data_is_labeled_but_renderable() {
        let health = SourceHealth::demo();
        assert!(health.is_demo());
        assert!(health.panels_renderable(), "labeled, not hidden");
        assert_eq!(health.banner("X"), Banner::Demo);
    }

    #[test]
    fn unconfigured_says_not_connected_and_hides_panels() {
        let health = SourceHealth::unconfigured();
        assert!(!health.panels_renderable());
        assert_eq!(
            health.banner("DEOS_CONSOLE_SOURCE"),
            Banner::NotConnected {
                hint: "DEOS_CONSOLE_SOURCE".into()
            }
        );
    }

    #[test]
    fn a_partially_unreachable_surface_is_a_load_error_not_an_empty_cta() {
        let health = SourceHealth {
            unreachable: vec!["computers".into()],
            ..SourceHealth::default()
        };
        // The page still renders (the answered surfaces show their data)…
        assert!(health.panels_renderable());
        assert_eq!(
            health.banner("X"),
            Banner::Partial {
                failed: vec!["computers".into()]
            }
        );
        // …but the failed surface must carry a load error, never a CTA.
        assert_eq!(health.surface_note("computers"), SurfaceNote::LoadError);
        assert_eq!(health.surface_note("hermeses"), SurfaceNote::Ok);
    }

    #[test]
    fn a_surface_the_source_does_not_serve_is_an_honest_empty() {
        let health = SourceHealth {
            unavailable: vec!["hermeses".into()],
            ..SourceHealth::default()
        };
        assert!(health.panels_renderable());
        assert_eq!(health.banner("X"), Banner::None);
        assert_eq!(health.surface_note("hermeses"), SurfaceNote::NotServed);
    }

    #[test]
    fn a_healthy_live_view_carries_no_banner() {
        let health = SourceHealth::default();
        assert!(health.panels_renderable());
        assert_eq!(health.banner("X"), Banner::None);
        assert_eq!(health.surface_note("anything"), SurfaceNote::Ok);
    }
}
