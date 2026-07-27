//! **The grain economy's VISUAL surface** — a CI pipeline / rented-grain run projected as a
//! serializable [`ViewNode`] tree, so a grain run paints in EVERY glass (cockpit gpui, browser
//! HTML, Discord embed, terminal) from ONE piece of DATA (renderer-independence), exactly like
//! the sibling forge card ([`crate::forge_card`]).
//!
//! ## Why a SELF-CONTAINED data model (no `agent-platform` / `dregg-doc` dep)
//!
//! The real concepts — a CWM charter of steps, an agent-platform grain LEASE (rent / meter /
//! reap), and the forge's proof-carrying CI gate (`docs/deos/DREGG-FORGE.md`: a CI pipeline is a
//! charter of steps run in a rented, metered, confined grain; a PR can be a bounty) — live in
//! excluded workspaces. Depending on them here would drag those graphs into `deos-view`'s tiny
//! renderer crate. So this module defines a PLAIN, serializable snapshot of those concepts
//! ([`GrainRun`] / [`LeaseView`] / [`StepView`] / [`BountyView`]) and renders THAT — the
//! SAME opaque-data-at-the-boundary decoupling the forge card ([`crate::forge_card`]) uses; the
//! live wiring (a `From` in agent-platform → [`GrainRun`]) is a thin follow-up.
//!
//! ## The tree it paints
//!
//! A `tabs` of two panels — **run** (the run title + the derived [`CheckGate`] verdict line, the
//! grain LEASE panel with a metered/budget budget bar + lease status, and the PIPELINE panel: the
//! charter steps as attributed rows with status pills + short terminal-receipt hashes) and
//! **bounty** (the PR-as-bounty state + reward, or the honest "direct rent" empty state). Every
//! empty case renders an HONEST empty state (never fabricated content).
//!
//! It is PURE `serde_json` + [`crate::tree`] (no `agent-platform`, no gpui, no mozjs), so it rides
//! ALL renderers: the ViewNode is built by [`crate::parse_view_tree`]-ing the canonical JSON,
//! guaranteeing [`grain_run_view`] and [`grain_run_view_json`] are the SAME tree, and the web
//! renderer ([`crate::web::render_html`], under `feature = "web"`) paints the identical card.

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use crate::tree::{parse_view_tree, ViewNode};

// ─────────────────────────────────────────────────────────────────────────────
// THE DATA MODEL — a plain, serializable snapshot of the grain-run's concepts.
// ─────────────────────────────────────────────────────────────────────────────

/// **The whole grain-run surface** — a titled run over a rented grain: its [`LeaseView`] (the
/// rent/meter/reap), its `pipeline` of charter [`StepView`]s, and an optional [`BountyView`] (the
/// PR-as-bounty). The CI gate is DERIVED from the pipeline ([`CheckGate::of`], mirroring the forge
/// card's derived [`crate::MergeGate`]), not stored, so the verdict can never disagree with the
/// steps it summarizes.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct GrainRun {
    /// The run's display title (the charter's name).
    pub title: String,
    /// The rented grain this run executes in (rent / meter / reap).
    pub lease: LeaseView,
    /// The CWM charter steps, in order (fetch → build → test → report), each a receipted advance.
    pub pipeline: Vec<StepView>,
    /// The PR-as-bounty state, if this run was offered as a bounty (else a direct rent).
    pub bounty: Option<BountyView>,
}

/// A **grain lease** — the rented, metered, confined body the run executes in (agent-platform's
/// grain lease). `host` names the executor; `metered`/`budget` are the spent/allotted meter (the
/// budget bar's numerator/denominator); `status` is the lifecycle (rent → meter → reap).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LeaseView {
    /// The executor host the grain is rented from.
    pub host: String,
    /// The meter spent so far (the budget bar's numerator).
    pub metered: u64,
    /// The meter allotted by the lease (the budget bar's denominator).
    pub budget: u64,
    /// The lease's lifecycle status.
    pub status: LeaseStatus,
}

/// A grain lease's lifecycle — rented-and-live, expired, or reclaimed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum LeaseStatus {
    /// Rented and live — the grain is metering.
    #[default]
    Active,
    /// The lease expired (its budget/time lapsed) but the grain is not yet reaped.
    Lapsed,
    /// The grain was reaped — its body reclaimed.
    Reaped,
}

impl LeaseStatus {
    /// A one-word label + the semantic palette tag the renderer tints the status pill.
    fn label_tag(self) -> (&'static str, &'static str) {
        match self {
            LeaseStatus::Active => ("active", "good"),
            LeaseStatus::Lapsed => ("lapsed", "warn"),
            LeaseStatus::Reaped => ("reaped", "bad"),
        }
    }
}

/// One **charter step** — a stage of the CI pipeline (fetch / build / test / report), each a
/// receipted advance in the confined grain. `receipt` is the short hash of the step's verified
/// turn (present once the step commits); a `None` receipt is a step that has not yet cleared.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StepView {
    /// The step's name (`fetch`, `build`, `test`, `report`).
    pub name: String,
    /// Its status.
    pub status: StepStatus,
    /// The short receipt hash of the step's verified turn, once it committed (`None` = not yet).
    pub receipt: Option<String>,
}

/// A charter step's status.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum StepStatus {
    /// The step's verified turn committed (its receipt is present).
    Done,
    /// The step is executing now.
    Running,
    /// The step has not started yet.
    Pending,
    /// The step's turn was refused / recorded a failure.
    Failed,
}

impl StepStatus {
    /// A one-word label + the semantic palette tag for the step pill.
    fn label_tag(self) -> (&'static str, &'static str) {
        match self {
            StepStatus::Done => ("done", "good"),
            StepStatus::Running => ("running", "accent"),
            StepStatus::Pending => ("pending", "muted"),
            StepStatus::Failed => ("failed", "bad"),
        }
    }
}

/// A **PR-as-bounty** — the run offered as a bounty a claimant runs for a reward. `reward` is the
/// display reward; `state` is the bounty lifecycle (open → claimed → submitted → paid).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BountyView {
    /// The reward on offer (a display string, e.g. `500 $DREGG`).
    pub reward: String,
    /// The bounty's lifecycle state.
    pub state: BountyState,
}

/// A bounty's lifecycle — offered → claimed by a runner → work submitted → paid out.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BountyState {
    /// Offered, unclaimed.
    Open,
    /// A runner claimed it (is working it).
    Claimed,
    /// The runner submitted their work (awaiting the merge gate).
    Submitted,
    /// The reward was paid out (a green run cleared the merge).
    Paid,
}

impl BountyState {
    /// A one-word label + the semantic palette tag for the bounty pill.
    fn label_tag(self) -> (&'static str, &'static str) {
        match self {
            BountyState::Open => ("open", "accent"),
            BountyState::Claimed => ("claimed", "warn"),
            BountyState::Submitted => ("submitted", "warn"),
            BountyState::Paid => ("paid", "good"),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE CI GATE — the one derived verdict the run header shows (mirrors `MergeGate`).
// ─────────────────────────────────────────────────────────────────────────────

/// **The CI-gate verdict** — the single derived answer the run header renders: does this run's
/// pipeline clear the merge? A `Failed` step refuses first; then a not-yet-complete pipeline is
/// `Running` (step k of n); else every step is `Done` AND the terminal step carries a receipt, so
/// the signed receipt clears the merge. An empty pipeline is the honest empty gate. Mirrors the
/// forge card's derived [`crate::MergeGate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckGate {
    /// Every step is `Done` and the terminal step carries a receipt — the signed receipt clears.
    Green,
    /// A step `Failed` — the merge is refused.
    Failed,
    /// The pipeline is still advancing — `done` of `total` steps have cleared.
    Running { done: usize, total: usize },
    /// The pipeline has no steps yet (the charter is empty).
    Empty,
}

impl CheckGate {
    /// Compute the gate for a pipeline (a failure dominates; then completeness + terminal receipt).
    pub fn of(pipeline: &[StepView]) -> CheckGate {
        if pipeline.is_empty() {
            return CheckGate::Empty;
        }
        if pipeline.iter().any(|s| s.status == StepStatus::Failed) {
            return CheckGate::Failed;
        }
        let done = pipeline
            .iter()
            .filter(|s| s.status == StepStatus::Done)
            .count();
        let total = pipeline.len();
        let terminal_receipt = pipeline
            .last()
            .map(|s| s.receipt.is_some())
            .unwrap_or(false);
        if done == total && terminal_receipt {
            CheckGate::Green
        } else {
            CheckGate::Running { done, total }
        }
    }

    /// The gate line's text + the semantic palette tag.
    fn label_tag(self) -> (String, &'static str) {
        match self {
            CheckGate::Green => (
                "✓ checks green · the signed receipt clears the merge".to_string(),
                "good",
            ),
            CheckGate::Failed => ("✗ CI failed · merge refused".to_string(), "bad"),
            CheckGate::Running { done, total } => (
                // `k` is the step now in flight (the next one after the cleared ones), clamped.
                format!("◷ running · step {} of {}", (done + 1).min(total), total),
                "warn",
            ),
            CheckGate::Empty => (
                "(no pipeline steps yet: the charter has no steps to run)".to_string(),
                "muted",
            ),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE VIEW-TREE BUILDERS  (pure serde_json, mirroring `forge_card`)
// ─────────────────────────────────────────────────────────────────────────────

/// A `deos.ui.text` node.
fn text(s: impl Into<String>) -> Value {
    json!({ "kind": "text", "props": { "text": s.into() } })
}

/// A `deos.ui.pill` node — a colored status badge (`tag` selects the semantic palette).
fn pill(s: impl Into<String>, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": s.into(), "tag": tag } })
}

/// A `deos.ui.row` node — a horizontal flex of children.
fn row(children: Vec<Value>) -> Value {
    json!({ "kind": "row", "props": {}, "children": children })
}

/// A `deos.ui.list` node — a vertical list of the child nodes.
fn list(children: Vec<Value>) -> Value {
    json!({ "kind": "list", "props": {}, "children": children })
}

/// A `deos.ui.vstack` node — a vertical column of the child nodes.
fn vstack(children: Vec<Value>) -> Value {
    json!({ "kind": "vstack", "props": {}, "children": children })
}

/// A `deos.ui.section` node — a titled, bordered container (`tag` = a styling accent).
fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

/// A `deos.ui.divider` node — a thin horizontal rule.
fn divider() -> Value {
    json!({ "kind": "divider", "props": {} })
}

/// A `deos.ui.progress` node — a STATIC (literal-valued) budget/progress bar. The card is a
/// self-contained snapshot (no live grain slots), so the meter is carried as a literal
/// `value`/`max` (baked into the fill by every renderer), not a bound `gauge`.
fn progress(value: u64, max: u64, label: &str) -> Value {
    json!({ "kind": "progress", "props": { "value": value, "max": max, "label": label } })
}

/// The lease panel: the host + a metered/budget budget bar + the lease-status pill, or an honest
/// empty state for an unrented run.
fn lease_panel(lease: &LeaseView) -> Value {
    let title = if lease.host.is_empty() {
        "lease".to_string()
    } else {
        format!("lease · {}", lease.host)
    };
    let (status_label, status_tag) = lease.status.label_tag();
    if lease.host.is_empty() && lease.budget == 0 && lease.metered == 0 {
        return section(
            &title,
            "",
            vec![text("(no grain rented yet: this run has no lease)")],
        );
    }
    let budget_label = format!("budget · {}/{} metered", lease.metered, lease.budget);
    section(
        &title,
        "genuine",
        vec![
            row(vec![
                pill("host", "muted"),
                text(if lease.host.is_empty() {
                    "(unrented)".to_string()
                } else {
                    lease.host.clone()
                }),
                pill(status_label, status_tag),
            ]),
            progress(lease.metered, lease.budget, &budget_label),
        ],
    )
}

/// The pipeline panel: the charter steps as attributed rows (a status pill + the step name + its
/// short terminal-receipt hash), or an honest empty state for a charter with no steps.
fn pipeline_panel(pipeline: &[StepView]) -> Value {
    if pipeline.is_empty() {
        return section(
            "pipeline",
            "",
            vec![text("(no steps yet: the charter has no steps to run)")],
        );
    }
    let step_rows: Vec<Value> = pipeline
        .iter()
        .map(|s| {
            let (label, tag) = s.status.label_tag();
            let mut cells = vec![pill(label, tag), text(s.name.clone())];
            match &s.receipt {
                Some(r) => cells.push(pill(format!("receipt {r}"), "accent")),
                None => cells.push(pill("no receipt", "muted")),
            }
            row(cells)
        })
        .collect();
    section(
        &format!("pipeline ({} steps)", pipeline.len()),
        "genuine",
        vec![list(step_rows)],
    )
}

/// The bounty panel: the bounty state + reward, or the honest "direct rent" empty state (this run
/// was not offered as a bounty).
fn bounty_panel(bounty: Option<&BountyView>) -> Value {
    let Some(b) = bounty else {
        return section(
            "bounty",
            "",
            vec![text("(not offered as a bounty: this run is a direct rent)")],
        );
    };
    let (label, tag) = b.state.label_tag();
    section(
        "bounty",
        "genuine",
        vec![row(vec![
            pill(label, tag),
            text(format!("reward · {}", b.reward)),
        ])],
    )
}

/// The run panel: the run title + the derived CI-gate line, then the lease panel and the pipeline
/// panel. The gate is derived ([`CheckGate::of`]) so it can never disagree with the steps.
fn run_panel(run: &GrainRun) -> Value {
    let gate = CheckGate::of(&run.pipeline);
    let (gate_label, gate_tag) = gate.label_tag();
    let title = if run.title.is_empty() {
        "grain-run".to_string()
    } else {
        format!("grain-run · {}", run.title)
    };
    let header = section(&title, "", vec![row(vec![pill(gate_label, gate_tag)])]);
    vstack(vec![
        header,
        lease_panel(&run.lease),
        divider(),
        pipeline_panel(&run.pipeline),
    ])
}

/// **The grain-run surface as a `deos.ui.*` view-tree** (a `serde_json::Value`) — a `tabs` of the
/// run panel (title + gate + lease + pipeline) and the bounty panel. The internal shape
/// [`grain_run_view`] parses.
fn grain_run_value(run: &GrainRun) -> Value {
    json!({
        "kind": "tabs",
        "props": {
            "tabs": ["run", "bounty"],
            "selectedSlot": 0,
            "selectTurn": "",
        },
        "children": [
            run_panel(run),
            bounty_panel(run.bounty.as_ref()),
        ],
    })
}

/// **The grain-run surface as a typed [`ViewNode`]** — the renderer-independent projection of
/// `run`. Hand it to ANY [`crate`] renderer (native gpui / web HTML / discord embed / the seL4
/// viewer) to paint the SAME card. Built by parsing the canonical JSON so this and
/// [`grain_run_view_json`] are guaranteed the identical tree.
pub fn grain_run_view(run: &GrainRun) -> ViewNode {
    // The JSON is authored in-crate (the canonical `{kind, props, children}` shape), so the parse
    // cannot fail; a malformed builder would fail this in tests immediately.
    parse_view_tree(&grain_run_view_json(run)).expect("the grain-run card JSON is well-formed")
}

/// **The grain-run surface as serialized `deos.ui.*` JSON** — byte-for-byte the shape a [`crate`]
/// renderer parses (via [`crate::parse_view_tree`]). This is the string the cockpit mount bridges
/// / a host serves.
pub fn grain_run_view_json(run: &GrainRun) -> String {
    serde_json::to_string(&grain_run_value(run)).expect("the grain-run card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Recursively collect every `serde_json` node of `kind` in a value tree.
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

    fn of_kind<'a>(v: &'a Value, kind: &str) -> Vec<&'a Value> {
        let mut out = Vec::new();
        collect(v, kind, &mut out);
        out
    }

    /// Does the serialized JSON contain `needle` anywhere (a paint-content assertion).
    fn json_has(run: &GrainRun, needle: &str) -> bool {
        grain_run_view_json(run).contains(needle)
    }

    fn sample_lease() -> LeaseView {
        LeaseView {
            host: "grain-host-7".to_string(),
            metered: 512,
            budget: 1000,
            status: LeaseStatus::Active,
        }
    }

    /// A full fetch→build→test→report pipeline, all `Done`, the terminal step receipted.
    fn all_done_pipeline() -> Vec<StepView> {
        vec![
            StepView {
                name: "fetch".to_string(),
                status: StepStatus::Done,
                receipt: Some("a1b2c3".to_string()),
            },
            StepView {
                name: "build".to_string(),
                status: StepStatus::Done,
                receipt: Some("d4e5f6".to_string()),
            },
            StepView {
                name: "test".to_string(),
                status: StepStatus::Done,
                receipt: Some("091827".to_string()),
            },
            StepView {
                name: "report".to_string(),
                status: StepStatus::Done,
                receipt: Some("aabbcc".to_string()),
            },
        ]
    }

    /// A clean all-`Done` run (terminal receipt present) shows the "checks green" gate.
    #[test]
    fn grain_run_clean_run_shows_checks_green() {
        let run = GrainRun {
            title: "verify the crate".to_string(),
            lease: sample_lease(),
            pipeline: all_done_pipeline(),
            bounty: None,
        };
        assert_eq!(CheckGate::of(&run.pipeline), CheckGate::Green);
        assert!(json_has(&run, "checks green"), "the green gate renders");
        assert!(json_has(&run, "verify the crate"), "the run title renders");
        // The terminal receipt hash paints on its step row.
        assert!(
            json_has(&run, "receipt aabbcc"),
            "the terminal receipt renders"
        );
        let _ = grain_run_view(&run);
    }

    /// A `Failed` step shows the "CI failed · merge refused" gate (a failure dominates).
    #[test]
    fn grain_run_failed_step_shows_ci_failed_merge_refused() {
        let mut pipeline = all_done_pipeline();
        pipeline[2].status = StepStatus::Failed;
        pipeline[2].receipt = None;
        let run = GrainRun {
            title: "broken build".to_string(),
            lease: sample_lease(),
            pipeline,
            bounty: None,
        };
        assert_eq!(CheckGate::of(&run.pipeline), CheckGate::Failed);
        assert!(json_has(&run, "CI failed"), "the failed gate renders");
        assert!(json_has(&run, "merge refused"), "the merge is refused");
        assert!(json_has(&run, "failed"), "the failed step pill renders");
        let _ = grain_run_view(&run);
    }

    /// A mid-run pipeline (some `Done`, one `Running`) shows the "step k of n" gate.
    #[test]
    fn grain_run_mid_run_shows_step_k_of_n() {
        let run = GrainRun {
            title: "in flight".to_string(),
            lease: sample_lease(),
            pipeline: vec![
                StepView {
                    name: "fetch".to_string(),
                    status: StepStatus::Done,
                    receipt: Some("a1b2c3".to_string()),
                },
                StepView {
                    name: "build".to_string(),
                    status: StepStatus::Running,
                    receipt: None,
                },
                StepView {
                    name: "test".to_string(),
                    status: StepStatus::Pending,
                    receipt: None,
                },
                StepView {
                    name: "report".to_string(),
                    status: StepStatus::Pending,
                    receipt: None,
                },
            ],
            bounty: None,
        };
        assert_eq!(
            CheckGate::of(&run.pipeline),
            CheckGate::Running { done: 1, total: 4 }
        );
        // 1 step done → the step now in flight is step 2 of 4.
        assert!(
            json_has(&run, "step 2 of 4"),
            "the running gate renders k of n"
        );
        assert!(json_has(&run, "running"), "the running step pill renders");
        let _ = grain_run_view(&run);
    }

    /// The lease budget bar carries the metered/budget meter (a static literal progress node).
    #[test]
    fn grain_run_lease_budget_gauge_renders_metered_over_budget() {
        let run = GrainRun {
            title: "metered run".to_string(),
            lease: sample_lease(),
            pipeline: all_done_pipeline(),
            bounty: None,
        };
        let tree = grain_run_value(&run);
        // A `progress` node carries the literal meter (value=metered, max=budget).
        let progresses = of_kind(&tree, "progress");
        assert_eq!(progresses.len(), 1, "one budget bar");
        assert_eq!(
            progresses[0]["props"]["value"], 512,
            "metered is the numerator"
        );
        assert_eq!(
            progresses[0]["props"]["max"], 1000,
            "budget is the denominator"
        );
        assert!(
            json_has(&run, "512/1000 metered"),
            "the meter label renders"
        );
        assert!(json_has(&run, "active"), "the lease status pill renders");
        let _ = grain_run_view(&run);
    }

    /// A bounty in EACH state renders its state pill + reward (the PR-as-bounty surface).
    #[test]
    fn grain_run_bounty_renders_in_each_state() {
        for (state, word) in [
            (BountyState::Open, "open"),
            (BountyState::Claimed, "claimed"),
            (BountyState::Submitted, "submitted"),
            (BountyState::Paid, "paid"),
        ] {
            let run = GrainRun {
                title: "bounty run".to_string(),
                lease: sample_lease(),
                pipeline: all_done_pipeline(),
                bounty: Some(BountyView {
                    reward: "500 $DREGG".to_string(),
                    state,
                }),
            };
            assert!(json_has(&run, word), "the {word} bounty pill renders");
            assert!(json_has(&run, "reward · 500 $DREGG"), "the reward renders");
        }
        // Absent bounty → the honest "direct rent" empty state.
        let no_bounty = GrainRun {
            title: "direct".to_string(),
            lease: sample_lease(),
            pipeline: all_done_pipeline(),
            bounty: None,
        };
        assert!(
            json_has(&no_bounty, "not offered as a bounty"),
            "the absent bounty says so"
        );
    }

    /// An EMPTY pipeline (and a default lease) renders honest empty states (no fabricated steps).
    #[test]
    fn grain_run_empty_pipeline_renders_honest_empty_state() {
        let run = GrainRun {
            title: "fresh".to_string(),
            lease: LeaseView::default(),
            pipeline: vec![],
            bounty: None,
        };
        assert_eq!(CheckGate::of(&run.pipeline), CheckGate::Empty);
        assert!(
            json_has(&run, "no pipeline steps yet") || json_has(&run, "no steps yet"),
            "the empty pipeline says so"
        );
        assert!(
            json_has(&run, "no grain rented yet"),
            "the empty lease says so"
        );
        // No step rows are fabricated (nothing to list).
        let tree = grain_run_value(&run);
        assert!(of_kind(&tree, "list").is_empty(), "nothing to list");
        let _ = grain_run_view(&run);
    }

    /// The serialized card is well-formed JSON in the canonical `{kind, props, children}` shape,
    /// and its top node is the `tabs` (run + bounty panels).
    #[test]
    fn grain_run_serializes_to_the_canonical_tabs_shape() {
        let run = GrainRun {
            title: "shape".to_string(),
            lease: sample_lease(),
            pipeline: all_done_pipeline(),
            bounty: None,
        };
        let s = grain_run_view_json(&run);
        let back: Value = serde_json::from_str(&s).expect("the grain-run card JSON parses");
        assert_eq!(back["kind"], "tabs");
        assert_eq!(back["props"]["tabs"][0], "run");
        assert_eq!(back["props"]["tabs"][1], "bounty");
        assert_eq!(
            back["children"].as_array().unwrap().len(),
            2,
            "the run panel + the bounty panel"
        );
    }

    // ── THE SAME CARD PAINTS IN THE BROWSER GLASS (renderer-independence) ──
    //    Under `feature = "web"` the IDENTICAL ViewNode walks into HTML — proving the grain-run
    //    card is renderer-independent, not native-only (mirroring the forge card's browser test).
    #[cfg(feature = "web")]
    #[test]
    fn grain_run_paints_in_the_browser_glass() {
        let run = GrainRun {
            title: "browser-paint proof".to_string(),
            lease: sample_lease(),
            pipeline: all_done_pipeline(),
            bounty: Some(BountyView {
                reward: "500 $DREGG".to_string(),
                state: BountyState::Paid,
            }),
        };
        // `BindValues` is a `[u64]` slice (the grain-run card has no `bind`/`gauge` nodes — its
        // budget bar is a static `progress` — so an empty slice is the whole first-paint snapshot).
        let empty: &[u64] = &[];
        let html = crate::web::render_html(&grain_run_view(&run), empty);
        assert!(!html.is_empty(), "the web renderer produced markup");
        // The SAME card content appears in the browser projection.
        assert!(
            html.contains("browser-paint proof"),
            "the run title paints in HTML"
        );
        assert!(html.contains("checks green"), "the CI gate paints in HTML");
        assert!(html.contains("paid"), "the bounty state paints in HTML");
    }
}
