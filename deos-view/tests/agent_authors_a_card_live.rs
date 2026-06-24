//! THE KEYSTONE LOOP, END TO END, PROVEN BY RUNNING — *a Claude rewrites its own
//! card's UI, accountably, while you watch.*
//!
//! This composes the already-landed pieces into ONE running demonstration:
//!
//!   1. THE AGENT'S HANDS — a `run_js`-shaped snippet authors a counter card's UI
//!      from a JS string via `deos.editor.editView` (the SAME `deos.editor.*` surface
//!      `deos-hermes::run_js` mounts under the agent's `held`, run here through
//!      `JsRuntime::run_authoring` — a real SpiderMonkey eval). The agent adds a `+1`
//!      button and relabels the title `Counter` → `Clicks`.
//!   2. ACCOUNTABLE — each authoring gesture is a real receipted patch: a provenance
//!      turn lands on the card's chain, and blame attributes every edit to the AGENT
//!      (`Author(99)`). The edit is an accountable patch, NOT a recompile.
//!   3. IT REACHES PIXELS — the re-folded view-source parses through the renderer's
//!      OWN `parse_view_tree`, and `deos-view` paints it to REAL gpui-component pixels.
//!      We capture BEFORE (the original counter card) and AFTER (with the agent's new
//!      button + relabel) PNGs that VISIBLY DIFFER.
//!   4. THE CAP TOOTH — an UNAUTHORIZED edit (a card whose `edit_authority` is `Proof`,
//!      held only at `Signature`) is REFUSED in-band: `editView` returns null, NO patch,
//!      NO turn, the view untouched.
//!
//! The agent's JS edit → a receipted patch → the re-folded view-tree carries the
//! change → it renders. That is the full hyperdreggmedia keystone loop, running.
//!
//! SpiderMonkey's `JSEngine::init()` is a PROCESS-GLOBAL one-shot AND the headless gpui
//! Metal renderer wants a big native stack, so the WHOLE loop runs in ONE `#[test]`, on
//! ONE engine, on ONE dedicated big-stack thread (JS authoring first, then render).
//!
//! Run: `cd deos-view && cargo test --release agent_authors_a_card_live -- --nocapture`

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::card_editor::{Author, CardEditor, ViewTree};
use deos_js::portable::{AffordanceSpec, ApplyOp, AppletManifest, PortableApplet};
use deos_js::{Applet, JsRuntime};
use dregg_cell::AuthRequired;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::{parse_view_tree, AppletView};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// The agent's blame identity — every patch the agent's JS lands is attributed to it.
const AGENT: Author = Author(99);

/// A counter card whose view is a structured view-tree (the shape deos-view paints): a
/// title text + a live count bind, a counter model, an `inc` affordance. This is the
/// card the agent adopts and authors.
fn counter_card_manifest() -> AppletManifest {
    let view = ViewTree::VStack {
        children: vec![
            ViewTree::Text {
                props: deos_js::card_editor::TextProps {
                    text: "Counter".into(),
                },
            },
            ViewTree::Bind {
                props: deos_js::card_editor::BindProps {
                    slot: 0,
                    label: "count: ".into(),
                },
            },
        ],
    };
    AppletManifest {
        seed_fields: vec![(0usize, 0u64)],
        affordances: vec![AffordanceSpec {
            name: "inc".into(),
            required: AuthRequired::Signature,
            op: ApplyOp::AddToSlot { slot: 0 },
        }],
        held: AuthRequired::Signature,
        view_source: view.to_json(),
    }
}

fn card_applet(seed: u8, manifest: &AppletManifest) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    PortableApplet::mint(pk, [0u8; 32], manifest)
}

/// Adopt a freshly-minted counter card for authoring under the given authority.
fn editor_for(seed: u8, held: AuthRequired, edit_authority: AuthRequired) -> CardEditor {
    let manifest = counter_card_manifest();
    let card = card_applet(seed, &manifest);
    CardEditor::adopt(card, manifest, AGENT, held, edit_authority)
}

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/agent-authoring");
    std::fs::create_dir_all(&dir).expect("create agent-authoring out dir");
    dir
}

#[test]
fn an_agent_authors_a_card_live_and_it_rerenders_accountably() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(body)
        .expect("spawn big-stack JS+render thread")
        .join()
        .expect("the loop thread");
}

fn body() {
    let out = out_dir();

    // ── BEFORE: render the unedited counter card (title + bind, NO button) → PNG #0 ──
    // The renderer consumes the card's structured view-source through its OWN parser —
    // proving the view-tree the editor folds IS what the renderer paints.
    let before_manifest = counter_card_manifest();
    let before_tree = parse_view_tree(&before_manifest.view_source)
        .expect("the card's structured view-source parses as a renderer view-tree");
    let before_applet = Rc::new(RefCell::new(card_applet(0xC0, &before_manifest)));

    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");

    let a0 = before_applet.clone();
    let t0 = before_tree.clone();
    let w0 = hr
        .open(420.0, 240.0, move |_window, cx| {
            cx.new(|_cx| AppletView::new(a0, t0))
        })
        .expect("open the unedited card window");
    let frame0 = hr.capture(w0.into()).expect("capture before-frame");
    let png_before = out.join("counter-before-agent.png");
    frame0.save(&png_before).expect("save before PNG");

    // ── THE AGENT'S HANDS — author the card from a JS string via deos.editor.* ───────
    // This is the run_js-shaped authoring path: the editor is mounted under the agent's
    // `held` (None admits the card's edit_authority=Signature — exactly run_js mounting
    // the editor under the agent's attenuated mandate), and the agent's JS calls
    // `deos.editor.editView` to add a button + relabel the title. Real SpiderMonkey.
    let mut rt = JsRuntime::new().expect("boot SpiderMonkey (process-global, once)");

    let editor = editor_for(0xC0, AuthRequired::None, AuthRequired::Signature);
    // The agent's actual snippet — its hands rewriting its own card's UI:
    let agent_js = r#"
        // The agent decides to make its counter card clickable + clearer.
        var card = deos.editor.card();                 // the editor's own card id
        // (1) add a "+1" button that fires the inc affordance — a structural patch.
        deos.editor.editView(card, {
            op: "addButton", label: "+1", affordance: "inc", arg: 1
        });
        // (2) relabel the title "Counter" -> "Clicks" — a second structural patch.
        var tree = deos.editor.editView(card, {
            op: "relabel", target: "Counter", text: "Clicks"
        });
        // Assert from JS that the re-folded tree carries BOTH changes.
        var hasButton = false, relabelled = false;
        (function walk(n) {
            if (!n) return;
            if (n.kind === "button" && n.props && n.props.on_click &&
                n.props.on_click.turn === "inc") hasButton = true;
            if (n.kind === "text" && n.props && n.props.text === "Clicks") relabelled = true;
            var kids = n.children || [];
            for (var i = 0; i < kids.length; i++) walk(kids[i]);
        })(tree);
        (hasButton && relabelled) ? 1 : 0;
    "#;
    let (result, editor) = rt
        .run_authoring(editor, agent_js)
        .expect("the agent's authoring run should succeed");
    assert_eq!(
        result,
        Some(1),
        "the agent's JS folded a view-tree with its new +1 button AND the relabel"
    );

    // ── ACCOUNTABLE: the agent's edits are receipted patches blamed on the agent ─────
    assert!(
        editor.view_tree().unwrap().has_button_for("inc"),
        "the card's current view-source folds to a tree carrying the agent's new button"
    );
    let receipt_count = editor.card().receipt_count();
    assert_eq!(
        receipt_count, 2,
        "the agent's two authoring gestures (addButton + relabel) each committed a \
         verified provenance turn on the card's chain"
    );
    let receipts: Vec<[u8; 32]> = editor.card().receipts().to_vec();
    assert!(
        receipts.iter().all(|h| h != &[0u8; 32]),
        "every authoring gesture left a real (non-zero) receipt"
    );
    assert!(
        editor.view_blame().iter().any(|l| l.author == AGENT),
        "blame attributes the view edits to the AGENT (Author 99) — accountable, not anonymous"
    );

    // The re-folded view-source parses through the renderer's OWN parser — the edited
    // structured view-tree IS renderable, and it carries the agent's new button node.
    let after_source = editor.view_source();
    let after_tree = parse_view_tree(&after_source)
        .expect("the agent's re-folded view-source parses as a renderer view-tree");
    assert!(
        node_has_inc_button(&after_tree),
        "the renderer's parse of the agent-authored card carries the inc button node"
    );

    // ── AFTER: render the agent-authored card (now WITH the button + relabel) → PNG #1 ─
    // Re-mint from the authored manifest so the rendered cell carries the agent's program.
    let after_applet = Rc::new(RefCell::new(editor.remint([0xC1; 32], [0u8; 32])));
    let a1 = after_applet.clone();
    let t1 = after_tree.clone();
    let w1 = hr
        .open(420.0, 240.0, move |_window, cx| {
            cx.new(|_cx| AppletView::new(a1, t1))
        })
        .expect("open the agent-authored card window");
    let frame1 = hr.capture(w1.into()).expect("capture after-frame");
    let png_after = out.join("counter-after-agent.png");
    frame1.save(&png_after).expect("save after PNG");

    // THE LOAD-BEARING ASSERTION: the agent-authored card renders DIFFERENTLY — its new
    // "+1" button + the "Clicks" relabel visibly appeared. The agent rewrote its own UI
    // from within, accountably, and the change reached pixels.
    assert_ne!(
        frame0.as_raw(),
        frame1.as_raw(),
        "the agent-authored card renders differently (the +1 button + relabel reached pixels)"
    );

    // ── THE CAP TOOTH: an UNAUTHORIZED edit is REFUSED in-band ───────────────────────
    // The agent holds Signature, but this card's authoring requires Proof — an over-reach.
    // `editView` returns null, no patch lands, no turn commits, the view is untouched.
    let overreach_editor = editor_for(0xCD, AuthRequired::Signature, AuthRequired::Proof);
    let overreach_js = r#"
        var card = deos.editor.card();
        // OVER-REACH: this card needs Proof, the agent holds only Signature.
        var refused = deos.editor.editView(card, {
            op: "addButton", label: "+1", affordance: "inc", arg: 1
        });
        (refused === null) ? 1 : 0;     // 1 iff the edit was refused in-band
    "#;
    let (refused_result, overreach_editor) = rt
        .run_authoring(overreach_editor, overreach_js)
        .expect("the over-reach run should succeed (refusal is in-band, not a fault)");
    assert_eq!(
        refused_result,
        Some(1),
        "the unauthorized editView was refused in-band (returned null)"
    );
    assert_eq!(
        overreach_editor.card().receipt_count(),
        0,
        "the refused edit committed NOTHING — no patch, no turn (the cap tooth holds)"
    );
    assert!(
        !overreach_editor.view_tree().unwrap().has_button_for("inc"),
        "the refused over-reach left the card's view untouched"
    );

    // ── THE REPORT ───────────────────────────────────────────────────────────────────
    println!("\n╭─ AN AGENT AUTHORED ITS OWN CARD LIVE — the hyperdreggmedia keystone loop ─╮");
    println!("│ what the agent's JS did:");
    println!("│   deos.editor.editView(card, addButton +1 → fires `inc`)");
    println!("│   deos.editor.editView(card, relabel \"Counter\" → \"Clicks\")");
    println!("│ accountable:");
    println!("│   receipted patches : {receipt_count} verified provenance turns on the card's chain");
    println!("│   blame             : every edit attributed to the agent ({AGENT:?})");
    println!("│   receipt[0]        : {}", hex8(&receipts[0]));
    println!("│   receipt[1]        : {}", hex8(&receipts[1]));
    println!("│ it reached pixels (real gpui-component, before/after DIFFER):");
    println!("│   before : {}", png_before.display());
    println!("│   after  : {}", png_after.display());
    println!("│ the cap tooth:");
    println!("│   an over-reach (Signature held, Proof required) was REFUSED in-band — no patch.");
    println!("╰───────────────────────────────────────────────────────────────────────────╯\n");
}

/// Walk a renderer `ViewNode` looking for a button whose onClick fires `inc`.
fn node_has_inc_button(node: &deos_view::ViewNode) -> bool {
    use deos_view::ViewNode;
    match node {
        ViewNode::Button { turn, .. } => turn == "inc",
        ViewNode::VStack(kids)
        | ViewNode::Row(kids)
        | ViewNode::List(kids)
        | ViewNode::Table(kids) => kids.iter().any(node_has_inc_button),
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
