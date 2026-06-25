//! THE REFLECTIVE-COCKPIT STEP — *a confined agent reflects-on a REAL cockpit surface,
//! then rewrites it live, accountably, while you watch.*
//!
//! `agent_authors_a_card_live` proved the keystone over a synthetic counter the test
//! invented. THIS proves the next rung of the hyperdreggmedia frontier
//! (`docs/deos/HYPERDREGGMEDIA.md` — "convert surfaces to cards so the agent rewrites the
//! real cockpit"): take a REAL cockpit surface — a **World-Status panel** (the inspector/
//! status face shape the desktop's `deos_desktop::viewnode_pane` / `card_pane` host: a
//! titled header over several live `bind` rows) — express it AS a `ViewNode` card whose
//! view is a function of state, and close the FULL reflective loop:
//!
//!   1. REFLECT-ON — the agent's JS calls `deos.editor.view()` (the READ half of the
//!      authoring surface) to read the live surface's OWN view-tree. It discovers the
//!      header + the three status rows IT DID NOT AUTHOR — it is reflecting on a real,
//!      pre-existing cockpit surface, not one it built. (A pure read: NO patch, NO turn.)
//!   2. REWRITE — having seen the surface, the agent rewrites it: it adds a `refresh`
//!      button (firing the panel's real `refresh` affordance) and relabels the header
//!      `World Status` → `World Status (live)`. Each gesture is a receipted patch, blamed
//!      on the AGENT (`Author(99)`) — an accountable patch, not a recompile.
//!   3. THE LIVE SURFACE RE-RENDERS — the re-folded view-tree parses through the renderer's
//!      OWN `parse_view_tree`, and the SAME native renderer the cockpit's panes use
//!      (`deos_view::AppletView`) paints it to REAL gpui-component pixels. BEFORE (the
//!      original panel) and AFTER (the agent's rewrite) PNGs VISIBLY DIFFER.
//!   4. PORTABLE — the IDENTICAL agent-rewritten tree also paints to the WEB backend
//!      (`ViewNode → HTML`): the rewritten surface is renderer-independent.
//!   5. THE CAP TOOTH — an over-reach (a panel whose authoring needs `Proof`, held only at
//!      `Signature`) is REFUSED in-band: no patch, no turn, the surface untouched.
//!
//! The agent reflected on the real cockpit surface → rewrote it → and the live surface
//! re-rendered, accountably. That is the reflective-cockpit loop, running.
//!
//! Run: `cd deos-view && cargo test --release agent_reflects_and_rewrites_a_surface_live -- --nocapture`
//! (web rung: add `--features web`).

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::card_editor::{Author, BindProps, CardEditor, TextProps, ViewTree};
use deos_js::portable::{AffordanceSpec, AppletManifest, ApplyOp, PortableApplet};
use deos_js::{Applet, JsRuntime};
use dregg_cell::AuthRequired;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::{AppletView, parse_view_tree};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// The agent's blame identity — every patch the agent's JS lands is attributed to it.
const AGENT: Author = Author(99);

/// The status panel's model slots — the live values its `bind` rows re-read off the
/// ledger (a status face is a function of state). `refreshes` is what the `refresh`
/// affordance bumps.
const SLOT_CELLS: usize = 0;
const SLOT_RECEIPTS: usize = 1;
const SLOT_REFRESHES: usize = 2;

/// **A REAL cockpit surface — the World-Status panel — AS a `ViewNode` card.** A titled
/// header over three live `bind` rows (the inspector/status face the desktop's
/// `viewnode_pane` / `card_pane` host), with a `refresh` affordance the panel can fire.
/// This is the surface the agent reflects-on and rewrites.
fn status_panel_manifest() -> AppletManifest {
    let view = ViewTree::VStack {
        children: vec![
            ViewTree::Text {
                props: TextProps {
                    text: "World Status".into(),
                },
            },
            ViewTree::Bind {
                props: BindProps {
                    slot: SLOT_CELLS,
                    label: "cells: ".into(),
                },
            },
            ViewTree::Bind {
                props: BindProps {
                    slot: SLOT_RECEIPTS,
                    label: "receipts: ".into(),
                },
            },
            ViewTree::Bind {
                props: BindProps {
                    slot: SLOT_REFRESHES,
                    label: "refreshes: ".into(),
                },
            },
        ],
    };
    AppletManifest {
        // The panel is a function of state — seed real witnessed values for its rows.
        seed_fields: vec![
            (SLOT_CELLS, 3u64),
            (SLOT_RECEIPTS, 12u64),
            (SLOT_REFRESHES, 0u64),
        ],
        affordances: vec![AffordanceSpec {
            name: "refresh".into(),
            required: AuthRequired::Signature,
            op: ApplyOp::AddToSlot {
                slot: SLOT_REFRESHES,
            },
        }],
        held: AuthRequired::Signature,
        view_source: view.to_json(),
    }
}

fn panel_applet(seed: u8, manifest: &AppletManifest) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    PortableApplet::mint(pk, [0u8; 32], manifest)
}

/// Adopt a freshly-minted status panel for authoring under the given authority.
fn editor_for(seed: u8, held: AuthRequired, edit_authority: AuthRequired) -> CardEditor {
    let manifest = status_panel_manifest();
    let card = panel_applet(seed, &manifest);
    CardEditor::adopt(card, manifest, AGENT, held, edit_authority)
}

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/agent-authoring");
    std::fs::create_dir_all(&dir).expect("create agent-authoring out dir");
    dir
}

#[test]
fn an_agent_reflects_on_a_cockpit_surface_and_rewrites_it_live() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(body)
        .expect("spawn big-stack JS+render thread")
        .join()
        .expect("the loop thread");
}

fn body() {
    let out = out_dir();

    // ── BEFORE: render the unedited status panel (header + 3 bind rows) → PNG #0 ──────
    let before_manifest = status_panel_manifest();
    let before_tree = parse_view_tree(&before_manifest.view_source)
        .expect("the panel's structured view-source parses as a renderer view-tree");
    let before_applet = Rc::new(RefCell::new(panel_applet(0xC0, &before_manifest)));

    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");

    let a0 = before_applet.clone();
    let t0 = before_tree.clone();
    let w0 = hr
        .open(420.0, 260.0, move |_window, cx| {
            cx.new(|_cx| AppletView::new(a0, t0))
        })
        .expect("open the unedited panel window");
    let frame0 = hr.capture(w0.into()).expect("capture before-frame");
    let png_before = out.join("status-panel-before-agent.png");
    frame0.save(&png_before).expect("save before PNG");

    // ── THE AGENT REFLECTS-ON, THEN REWRITES — its hands on a REAL cockpit surface ────
    let mut rt = JsRuntime::new().expect("boot SpiderMonkey (process-global, once)");

    let editor = editor_for(0xC0, AuthRequired::None, AuthRequired::Signature);
    let agent_js = r#"
        // (0) REFLECT-ON — read the live surface's OWN view-tree before touching it.
        // The agent did NOT build this surface; it is reading a real cockpit panel.
        var surface = deos.editor.view();
        var sawHeader = false, statusRows = 0;
        (function walk(n) {
            if (!n) return;
            if (n.kind === "text" && n.props && n.props.text === "World Status") sawHeader = true;
            if (n.kind === "bind") statusRows += 1;
            var kids = n.children || [];
            for (var i = 0; i < kids.length; i++) walk(kids[i]);
        })(surface);
        // It must have reflected the pre-existing header + all three status rows.
        var reflected = sawHeader && (statusRows === 3);

        // (1) REWRITE — having seen the surface, add a `refresh` button (fires the
        //     panel's real `refresh` affordance) — a structural patch.
        var card = deos.editor.card();
        deos.editor.editView(card, {
            op: "addButton", label: "refresh", affordance: "refresh", arg: 1
        });
        // (2) relabel the header "World Status" -> "World Status (live)".
        var tree = deos.editor.editView(card, {
            op: "relabel", target: "World Status", text: "World Status (live)"
        });

        // Assert from JS that the re-folded tree carries BOTH rewrites.
        var hasButton = false, relabelled = false;
        (function walk(n) {
            if (!n) return;
            if (n.kind === "button" && n.props && n.props.on_click &&
                n.props.on_click.turn === "refresh") hasButton = true;
            if (n.kind === "text" && n.props && n.props.text === "World Status (live)")
                relabelled = true;
            var kids = n.children || [];
            for (var i = 0; i < kids.length; i++) walk(kids[i]);
        })(tree);
        (reflected && hasButton && relabelled) ? 1 : 0;
    "#;
    let (result, editor) = rt
        .run_authoring(editor, agent_js)
        .expect("the agent's reflect-then-rewrite run should succeed");
    assert_eq!(
        result,
        Some(1),
        "the agent reflected the real surface (header + 3 rows), then re-folded a tree \
         with its refresh button AND the relabel"
    );

    // ── ACCOUNTABLE: the agent's rewrites are receipted patches blamed on the agent ──
    assert!(
        editor.view_tree().unwrap().has_button_for("refresh"),
        "the panel's current view-source folds to a tree carrying the agent's refresh button"
    );
    let receipt_count = editor.card().receipt_count();
    assert_eq!(
        receipt_count, 2,
        "the agent's two rewrite gestures (addButton + relabel) each committed a verified \
         provenance turn on the surface's chain"
    );
    let receipts: Vec<[u8; 32]> = editor.card().receipts().to_vec();
    assert!(
        receipts.iter().all(|h| h != &[0u8; 32]),
        "every rewrite gesture left a real (non-zero) receipt"
    );
    assert!(
        editor.view_blame().iter().any(|l| l.author == AGENT),
        "blame attributes the surface rewrites to the AGENT (Author 99) — accountable"
    );

    // The re-folded view-source parses through the renderer's OWN parser — the rewritten
    // surface IS renderable, and it carries the agent's new refresh-button node.
    let after_source = editor.view_source();
    let after_tree = parse_view_tree(&after_source)
        .expect("the agent's rewritten view-source parses as a renderer view-tree");
    assert!(
        node_has_refresh_button(&after_tree),
        "the renderer's parse of the agent-rewritten panel carries the refresh button node"
    );

    // ── AFTER: render the agent-rewritten panel (now WITH the button + relabel) → PNG #1
    let after_applet = Rc::new(RefCell::new(editor.remint([0xC1; 32], [0u8; 32])));
    let a1 = after_applet.clone();
    let t1 = after_tree.clone();
    let w1 = hr
        .open(420.0, 260.0, move |_window, cx| {
            cx.new(|_cx| AppletView::new(a1, t1))
        })
        .expect("open the agent-rewritten panel window");
    let frame1 = hr.capture(w1.into()).expect("capture after-frame");
    let png_after = out.join("status-panel-after-agent.png");
    frame1.save(&png_after).expect("save after PNG");

    // THE LOAD-BEARING ASSERTION: the agent-rewritten surface renders DIFFERENTLY — the
    // refresh button + the `(live)` relabel reached pixels. The agent reflected on a real
    // cockpit surface and rewrote it live, and the change reached the glass.
    assert_ne!(
        frame0.as_raw(),
        frame1.as_raw(),
        "the agent-rewritten panel renders differently (refresh button + relabel reached pixels)"
    );

    // ── PORTABLE: the SAME agent-rewritten ViewNode tree renders to the WEB backend ──
    #[cfg(feature = "web")]
    let web_after_path = {
        use deos_view::{render_card_document, render_html};

        // Paint each surface's bind rows with the panel's witnessed values (3 cells,
        // 12 receipts, 0 refreshes — tree-walk order).
        let binds = [3u64, 12, 0];
        let web_before = render_html(&before_tree, &binds);
        let web_after = render_html(&after_tree, &binds);

        assert!(
            web_after.contains(
                r#"<button class="deos-button" data-turn="refresh" data-arg="1">refresh</button>"#
            ),
            "the web render of the agent-rewritten panel carries the refresh button's REAL affordance"
        );
        assert!(
            web_after.contains(r#"<span class="deos-text">World Status (live)</span>"#),
            "the web render carries the agent's `World Status`→`World Status (live)` relabel"
        );
        assert!(
            !web_before.contains(r#"data-turn="refresh""#)
                && web_before.contains(r#"<span class="deos-text">World Status</span>"#),
            "the unedited panel's web render had NO refresh button and the original header"
        );
        assert!(
            web_after.contains(r#"<span class="deos-bind" data-slot="1">receipts: 12</span>"#),
            "the status rows (a function of state) still paint their witnessed values"
        );
        assert_ne!(
            web_before, web_after,
            "native (pixels) AND web (HTML) BOTH re-painted the agent's rewrite — the SAME \
             agent-rewritten ViewNode surface, two renderers: the cockpit surface is PORTABLE"
        );

        let doc = render_card_document("agent-rewritten World-Status panel", &after_tree, &binds);
        let html_path = out.join("status-panel-after-agent.html");
        std::fs::write(&html_path, &doc).expect("write the agent-rewritten panel's web bake");
        html_path
    };

    // ── THE CAP TOOTH: an over-reach is REFUSED in-band ──────────────────────────────
    // This panel's authoring requires Proof; the agent holds only Signature.
    let overreach_editor = editor_for(0xCD, AuthRequired::Signature, AuthRequired::Proof);
    let overreach_js = r#"
        var card = deos.editor.card();
        // The agent can still REFLECT (read) — reflection is unprivileged.
        var surface = deos.editor.view();
        var sawHeader = (surface && surface.kind === "vstack");
        // But the REWRITE over-reaches: this panel needs Proof, the agent holds Signature.
        var refused = deos.editor.editView(card, {
            op: "addButton", label: "refresh", affordance: "refresh", arg: 1
        });
        (sawHeader && refused === null) ? 1 : 0;
    "#;
    let (refused_result, overreach_editor) = rt
        .run_authoring(overreach_editor, overreach_js)
        .expect("the over-reach run should succeed (refusal is in-band, not a fault)");
    assert_eq!(
        refused_result,
        Some(1),
        "the agent could reflect (read) but the unauthorized rewrite was refused in-band (null)"
    );
    assert_eq!(
        overreach_editor.card().receipt_count(),
        0,
        "the refused rewrite committed NOTHING — no patch, no turn (the cap tooth holds)"
    );
    assert!(
        !overreach_editor
            .view_tree()
            .unwrap()
            .has_button_for("refresh"),
        "the refused over-reach left the surface's view untouched"
    );

    // ── THE REPORT ───────────────────────────────────────────────────────────────────
    println!("\n╭─ AN AGENT REFLECTED ON A REAL COCKPIT SURFACE + REWROTE IT LIVE ─╮");
    println!("│ the surface : a World-Status panel (header + 3 live bind rows) as a ViewNode card");
    println!("│ reflect-on  : deos.editor.view() — the agent read the surface's own tree");
    println!("│               (saw the header + 3 status rows it did NOT author)");
    println!("│ rewrite     :");
    println!("│   deos.editor.editView(card, addButton refresh → fires `refresh`)");
    println!("│   deos.editor.editView(card, relabel \"World Status\" → \"World Status (live)\")");
    println!("│ accountable :");
    println!(
        "│   receipted patches : {receipt_count} verified provenance turns on the surface's chain"
    );
    println!("│   blame             : every rewrite attributed to the agent ({AGENT:?})");
    println!("│   receipt[0]        : {}", hex8(&receipts[0]));
    println!("│   receipt[1]        : {}", hex8(&receipts[1]));
    println!("│ the live surface re-rendered (real gpui-component, before/after DIFFER):");
    println!("│   before : {}", png_before.display());
    println!("│   after  : {}", png_after.display());
    #[cfg(feature = "web")]
    {
        println!("│ portable — the SAME rewritten surface also renders to the web:");
        println!("│   web    : {}", web_after_path.display());
    }
    println!(
        "│ the cap tooth: an over-reach (Signature held, Proof required) was REFUSED — no patch."
    );
    println!("╰──────────────────────────────────────────────────────────────────╯\n");
}

/// Walk a renderer `ViewNode` looking for a button whose onClick fires `refresh`.
fn node_has_refresh_button(node: &deos_view::ViewNode) -> bool {
    use deos_view::ViewNode;
    match node {
        ViewNode::Button { turn, .. } => turn == "refresh",
        ViewNode::VStack(kids)
        | ViewNode::Row(kids)
        | ViewNode::List(kids)
        | ViewNode::Table(kids) => kids.iter().any(node_has_refresh_button),
        _ => false,
    }
}

fn hex8(h: &[u8; 32]) -> String {
    let mut s = String::with_capacity(16);
    for b in &h[..8] {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
