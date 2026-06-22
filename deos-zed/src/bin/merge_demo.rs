//! merge_demo — TWO authors branch a shared document, edit offline, merge, and
//! the result is shown in the [`DocViewer`]: clean where disjoint, a first-class
//! CONFLICT OBJECT where they genuinely clash.
//!
//! Two modes (same shape as the editor demo):
//!
//!   * `merge_demo` (default): open a gpui window showing the merged document's
//!     structure — the blame timeline and the conflict object (both alternatives
//!     + authorship), NOT a `<<<<<<<` text wound.
//!
//!   * `merge_demo --verify`: headless. Build the merge and assert it has the
//!     expected clean regions + conflict object, printing the structure. Exits 0
//!     on success. The CI-runnable proof of the multi-author merge.

use dregg_doc::{Author, Granularity, Rendered, RopeDoc, Segment};
use ropey::Rope;

fn rope(s: &str) -> Rope {
    Rope::from_str(s)
}

/// Build the demo merge: a shared document, two offline co-author branches (one
/// disjoint edit each + one clashing edit), merged into one document carrying both
/// the clean edits AND a conflict object. Returns the merged document.
fn build_merge() -> RopeDoc {
    // The shared document both authors opened. The disjoint edits live in the
    // clean PREFIX; the line both authors will fight over is at the TAIL — so the
    // merge renders the whole clean prefix (both disjoint edits land) and then the
    // first-class conflict object. (The renderer linearizes the clean prefix and
    // stops at the first genuine fork — content after a fork is reachable only
    // through a chosen alternative, i.e. only once the conflict is resolved.)
    let mut shared = RopeDoc::new(Granularity::Line);
    shared.edit_rope(
        Author(1),
        &rope("# Project Plan\n\nintro\n\nstatus: open\n"),
    );

    // Two offline branches (open-the-same-file, edit-apart).
    let mut alice = shared.branch();
    let mut bob = shared.branch();

    // Alice: rewrite the intro (disjoint, in the prefix) AND set the status tail.
    alice.edit_rope(
        Author(1),
        &rope("# Project Plan\n\nthe real intro, by alice\n\nstatus: shipping\n"),
    );
    // Bob: keep the intro, set a DIFFERENT status tail (the clash).
    bob.edit_rope(
        Author(2),
        &rope("# Project Plan\n\nintro\n\nstatus: blocked\n"),
    );

    // Merge Bob into Alice — the pushout. The disjoint intro rewrite lands in the
    // clean prefix; the clashing status line becomes a first-class conflict object.
    let mut merged = alice.branch();
    let _ = merged.merge_branch(&bob);
    merged
}

/// Print the rendered structure of a merge: clean runs and conflict objects, each
/// alternative attributed to its author.
fn print_structure(r: &Rendered) {
    for (i, seg) in r.segments.iter().enumerate() {
        match seg {
            Segment::Clean(t) => {
                for line in t.lines() {
                    println!("  [{i:>2}] clean   | {line}");
                }
            }
            Segment::Conflict(c) => {
                println!("  [{i:>2}] CONFLICT ({}):", c.regime.label());
                for alt in &c.alternatives {
                    println!(
                        "         ↳ @{} : {}",
                        alt.provenance.author.0,
                        alt.text.trim_end_matches('\n')
                    );
                }
            }
        }
    }
}

fn verify() -> anyhow::Result<()> {
    let merged = build_merge();
    let r = merged.rendered();
    println!("merged document structure ({} patches):", merged.history().len());
    print_structure(&r);

    anyhow::ensure!(r.has_conflict(), "the clashing owner line must be a conflict object");
    let conflict = r.conflicts().next().expect("a conflict region");
    anyhow::ensure!(
        conflict.alternatives.len() == 2,
        "two pens at one tail => two alternatives"
    );
    let authors: Vec<u64> = conflict.alternatives.iter().map(|a| a.provenance.author.0).collect();
    anyhow::ensure!(
        authors.contains(&1) && authors.contains(&2),
        "both authors attributed in the conflict object"
    );

    // The disjoint intro rewrite landed cleanly in the prefix.
    let text = r.to_marked_string();
    anyhow::ensure!(text.contains("by alice"), "Alice's intro rewrite landed clean in the prefix");
    // The clash is over the status line — both alternatives are in the object.
    let alts: Vec<&str> = conflict.alternatives.iter().map(|a| a.text.trim_end()).collect();
    anyhow::ensure!(
        alts.iter().any(|t| t.contains("shipping")) && alts.iter().any(|t| t.contains("blocked")),
        "both status alternatives are in the conflict object"
    );

    println!("\nVERIFIED — the disjoint intro rewrite merged clean (clean prefix); the clashing");
    println!("status line is a first-class conflict object carrying BOTH alternatives +");
    println!("authorship (no `<<<<<<<` wound).");
    Ok(())
}

fn main() -> anyhow::Result<()> {
    let headless = std::env::args().any(|a| a == "--verify" || a == "--headless");
    if headless {
        return verify();
    }
    #[cfg(feature = "gui-demo")]
    {
        gui::run();
        Ok(())
    }
    #[cfg(not(feature = "gui-demo"))]
    {
        eprintln!(
            "merge_demo: built without `gui-demo`.\n\
             Run `cargo run --bin merge_demo --features gui-demo` for the window, or\n\
             `cargo run --bin merge_demo -- --verify` for the headless merge proof."
        );
        verify()
    }
}

#[cfg(feature = "gui-demo")]
mod gui {
    use super::build_merge;
    use deos_zed::DocViewer;
    use gpui::{
        div, px, size, App, AppContext as _, Context, Entity, FocusHandle, Focusable,
        InteractiveElement as _, IntoElement, ParentElement as _, Render, Styled as _, Window,
        WindowBounds, WindowOptions,
    };
    use gpui_component::{h_flex, v_flex, ActiveTheme as _, Root, TitleBar};

    struct MergeDemo {
        viewer: Entity<DocViewer>,
        focus: FocusHandle,
    }

    impl MergeDemo {
        fn new(_window: &mut Window, cx: &mut Context<Self>) -> Self {
            let merged = build_merge();
            let viewer = cx.new(|cx| DocViewer::from_doc(&merged, "Project Plan (merged)", cx));
            Self { viewer, focus: cx.focus_handle() }
        }
    }

    impl Focusable for MergeDemo {
        fn focus_handle(&self, _: &App) -> FocusHandle {
            self.focus.clone()
        }
    }

    impl Render for MergeDemo {
        fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
            v_flex()
                .size_full()
                .track_focus(&self.focus)
                .child(TitleBar::new().child(
                    "deos-zed — two authors merged: blame timeline + the conflict object",
                ))
                .child(
                    h_flex().flex_1().min_h(px(0.)).child(
                        div()
                            .flex_1()
                            .h_full()
                            .border_l_1()
                            .border_color(cx.theme().border)
                            .child(self.viewer.clone()),
                    ),
                )
        }
    }

    pub fn run() {
        let app = gpui_platform::application().with_assets(gpui_component_assets::Assets);
        app.run(move |cx| {
            gpui_component::init(cx);
            cx.activate(true);
            let opts = WindowOptions {
                window_bounds: Some(WindowBounds::centered(size(px(900.), px(680.)), cx)),
                ..Default::default()
            };
            cx.spawn(async move |cx| {
                cx.open_window(opts, |window, cx| {
                    let view = cx.new(|cx| MergeDemo::new(window, cx));
                    cx.new(|cx| Root::new(view, window, cx))
                })
                .expect("open window");
            })
            .detach();
        });
    }
}
