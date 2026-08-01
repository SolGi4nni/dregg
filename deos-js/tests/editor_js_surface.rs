//! THE CARD EDITOR AS A JS SURFACE, PROVEN BY RUNNING — `deos.editor.{editView,
//! setField, addAffordance}` authors a card LIVE from inside a JS string, the same
//! shape `deos-hermes::run_js` drives.
//!
//! A user OR an agent (via run_js) authors a card's UI/state from within the image:
//!   (a) `deos.editor.editView(card, {op:"addButton",...})` adds a button → the
//!       re-folded view-tree CONTAINS it · a receipted patch landed · blame attributes
//!       it (the keystone: edit-the-UI-from-within → re-render → accountable patch);
//!   (b) `deos.editor.setField(card, slot, value)` is a real `SetField` verified turn
//!       (a re-read reflects it);
//!   (c) `deos.editor.addAffordance(card, spec)` welds a fireable affordance (the card
//!       fires it afterward);
//!   (d) an UNAUTHORIZED edit (a card outside the editor's reach) is REFUSED in-band —
//!       no patch, no turn, returns null/-1;
//!   (e) the AGENT-flavored proof — a run_js-style snippet authors an authorized card's
//!       UI from a JS string, bounded by `held`.
//!
//! SpiderMonkey is a process-global, thread-bound singleton (`JSEngine::init()` once
//! per process), so EVERY phase runs in ONE `#[test]`, on ONE engine, on a dedicated
//! big-stack thread (the harness's ~2MB worker stack underflows SM's quota guard).

use deos_js::card_editor::{CardEditor, ViewTree};
use deos_js::js::JsRuntime;
use deos_js::portable::{AffordanceSpec, AppletManifest, ApplyOp, PortableApplet};
use dregg_cell::AuthRequired;
use dregg_cell::Credential;
use dregg_cell::Requirement;
use dregg_doc::Author;

/// A card whose view is a structured view-tree (the shape deos-view paints): a title +
/// a live count bind, a counter model, an `inc` affordance.
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
                    label: "count".into(),
                },
            },
        ],
    };
    AppletManifest {
        seed_fields: vec![(0usize, 0u64)],
        affordances: vec![AffordanceSpec {
            name: "inc".into(),
            required: Requirement::AtLeast(Credential::Signature),
            op: ApplyOp::AddToSlot { slot: 0 },
        }],
        held: AuthRequired::Signature,
        view_source: view.to_json(),
    }
}

/// Mint a card + adopt it for authoring under `held`/`edit_authority`. `author` is the
/// blame identity every patch is attributed to.
fn editor_with(
    pk0: u8,
    author: Author,
    held: AuthRequired,
    edit_authority: Requirement,
) -> CardEditor {
    let manifest = counter_card_manifest();
    let mut pk = [0u8; 32];
    pk[0] = pk0;
    let card = PortableApplet::mint(pk, [0u8; 32], &manifest);
    CardEditor::adopt(card, manifest, author, held, edit_authority)
}

#[test]
fn js_authors_a_card_via_deos_editor() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(editor_js_body)
        .expect("spawn big-stack JS thread")
        .join()
        .expect("editor JS thread");
}

fn editor_js_body() {
    let mut rt = JsRuntime::new().expect("boot SpiderMonkey (process-global, once)");

    // ── (a) EDIT THE VIEW from a JS string — the keystone. ─────────────────────────
    // The editor is authorized (held=None admits the card's edit_authority=Signature).
    let editor = editor_with(
        0xCA,
        Author(7),
        AuthRequired::None,
        Requirement::AtLeast(Credential::Signature),
    );
    let js_a = r#"
        var card = deos.editor.card();            // the editor's own card id
        // add a "+1" button (fires the inc affordance) — a structural view PATCH.
        var tree = deos.editor.editView(card, {
            op: "addButton", label: "+1", affordance: "inc", arg: 1
        });
        // assert from JS the re-folded tree carries the new button.
        var hasButton = false;
        (function walk(n) {
            if (!n) return;
            if (n.kind === "button" && n.props && n.props.on_click &&
                n.props.on_click.turn === "inc") hasButton = true;
            var kids = n.children || [];
            for (var i = 0; i < kids.length; i++) walk(kids[i]);
        })(tree);
        hasButton ? 1 : 0;
    "#;
    let (result, editor) = rt
        .run_authoring(editor, js_a)
        .expect("authoring run (a) should succeed");
    assert_eq!(
        result,
        Some(1),
        "the JS-folded view-tree carries the inc button it just added"
    );
    // The Rust side ALSO sees the re-folded view + the receipted patch + the blame.
    assert!(
        editor.view_tree().unwrap().has_button_for("inc"),
        "the card's current view-source folds to a tree with the new button"
    );
    assert_eq!(
        editor.card().receipt_count(),
        1,
        "exactly one verified turn (the authorship provenance) committed for the view-edit"
    );
    assert!(
        editor.view_blame().iter().any(|l| l.author == Author(7)),
        "the JS view-patch is blamed on its author (the accountable patch)"
    );

    // ── (b) EDIT A FIELD from JS — a real verified turn. ───────────────────────────
    let editor = editor_with(
        0xCB,
        Author(7),
        AuthRequired::None,
        Requirement::AtLeast(Credential::Signature),
    );
    let js_b = r#"
        var card = deos.editor.card();
        var ok = deos.editor.setField(card, 0, 42);   // a real SetField turn
        ok;                                            // 1 on commit
    "#;
    let (result, editor) = rt
        .run_authoring(editor, js_b)
        .expect("authoring run (b) should succeed");
    assert_eq!(result, Some(1), "setField committed a verified turn");
    assert_eq!(
        editor.card().get_u64(0),
        42,
        "a re-read reflects the field set via a JS-driven verified turn"
    );
    assert_eq!(
        editor.card().receipt_count(),
        1,
        "one verified turn committed"
    );

    // ── (c) ADD AN AFFORDANCE from JS — a new fireable turn. ───────────────────────
    let editor = editor_with(
        0xCC,
        Author(7),
        AuthRequired::None,
        Requirement::AtLeast(Credential::Signature),
    );
    let js_c = r#"
        var card = deos.editor.card();
        // weld a "dec" affordance (subtract from slot 0).
        var ok = deos.editor.addAffordance(card, {
            name: "dec", required: "signature", op: "sub", slot: 0
        });
        ok;
    "#;
    let (result, mut editor) = rt
        .run_authoring(editor, js_c)
        .expect("authoring run (c) should succeed");
    assert_eq!(result, Some(1), "addAffordance committed the weld");
    // The welded affordance FIRES afterward (it is live on the card).
    editor.set_field(0, 10).unwrap();
    let fire = editor
        .card_mut()
        .fire("dec", 3)
        .expect("the JS-welded affordance fires a real verified turn");
    assert_ne!(
        fire.receipt_hash(),
        [0u8; 32],
        "the welded affordance fired a real turn"
    );
    assert_eq!(
        editor.card().get_u64(0),
        7,
        "10 - 3 via the JS-welded affordance"
    );

    // ── (d) AN UNAUTHORIZED edit is REFUSED in-band — no patch, no turn. ───────────
    // Two distinct over-reaches refused at the JS surface:
    //   (d.1) the cap tooth — held(Signature) does NOT satisfy edit_authority(Proof);
    //   (d.2) the wrong card — a cardId that is NOT the editor's own.
    let editor = editor_with(
        0xCD,
        Author(99),
        AuthRequired::Signature,
        Requirement::AtLeast(Credential::Proof),
    );
    let js_d = r#"
        var card = deos.editor.card();
        // (d.1) over-reach the cap: the card needs Proof, the editor holds Signature.
        var refusedCap = deos.editor.editView(card, {
            op: "addButton", label: "+1", affordance: "inc", arg: 1
        });
        // (d.2) author a DIFFERENT card id than the editor's — the wrong-card over-reach.
        var elsewhere = "00".repeat ? "00".repeat(64) :
            (function(){ var s=""; for (var i=0;i<64;i++) s+="0"; return s; })();
        var refusedField = deos.editor.setField(elsewhere, 0, 1);
        // pack: both refused (null / -1) → 1, else 0.
        (refusedCap === null && refusedField === -1) ? 1 : 0;
    "#;
    let (result, editor) = rt
        .run_authoring(editor, js_d)
        .expect("authoring run (d) should succeed (refusal is in-band, not a fault)");
    assert_eq!(
        result,
        Some(1),
        "the cap-over-reach returned null AND the wrong-card edit returned -1"
    );
    assert_eq!(
        editor.card().receipt_count(),
        0,
        "the refused edits committed NOTHING (no patch, no turn — the bound holds)"
    );
    assert!(
        !editor.view_tree().unwrap().has_button_for("inc"),
        "the refused view-edit left the card's view untouched"
    );

    // ── (e) THE AGENT DOES IT — a run_js-style snippet authors an authorized card. ──
    // The agent (Author 99) holds a broad-but-attenuated mandate (held=None) that
    // satisfies the card's authoring authority (Signature) — exactly run_js mounting
    // the editor under the agent's `held`. It authors the card's UI live, accountably.
    let editor = editor_with(
        0xA6,
        Author(99),
        AuthRequired::None,
        Requirement::AtLeast(Credential::Signature),
    );
    let js_e = r#"
        // The agent's snippet: build its OWN card UI from inside the image.
        var card = deos.editor.card();
        deos.editor.editView(card, { op: "addText", text: "authored by the agent" });
        deos.editor.editView(card, {
            op: "addButton", label: "reset", affordance: "reset", arg: 0
        });
        deos.editor.setField(card, 0, 1);          // and seed the model.
        var tree = deos.editor.editView(card, { op: "relabel", target: "Counter", text: "Clicks" });
        // assert the agent's whole authored UI from JS: the reset button is present
        // and the title was relabelled.
        var hasReset = false, relabelled = false;
        (function walk(n) {
            if (!n) return;
            if (n.kind === "button" && n.props && n.props.on_click &&
                n.props.on_click.turn === "reset") hasReset = true;
            if (n.kind === "text" && n.props && n.props.text === "Clicks") relabelled = true;
            var kids = n.children || [];
            for (var i = 0; i < kids.length; i++) walk(kids[i]);
        })(tree);
        (hasReset && relabelled) ? 1 : 0;
    "#;
    let (result, editor) = rt
        .run_authoring(editor, js_e)
        .expect("agent authoring run (e) should succeed");
    assert_eq!(
        result,
        Some(1),
        "the agent authored its card's UI from a JS string: reset button + relabel landed"
    );
    // The agent's gestures are accountable: blame attributes them to the agent, and
    // the field-set + structural patches each committed a verified turn.
    assert!(
        editor.view_blame().iter().any(|l| l.author == Author(99)),
        "every agent edit is blamed on the agent (the accountable patch)"
    );
    assert_eq!(
        editor.card().get_u64(0),
        1,
        "the agent's JS-driven setField is a real verified turn (re-read reflects it)"
    );
    // 4 authoring gestures (addText, addButton, setField, relabel) → 4 verified turns.
    assert_eq!(
        editor.card().receipt_count(),
        4,
        "the agent's four authoring gestures each committed a verified turn, bounded by held"
    );

    // The authored card is a PORTABLE cell — re-mint it and the welded UI/program travel.
    let mut pk = [0u8; 32];
    pk[0] = 0xBE;
    let reminted = editor.remint(pk, [0u8; 32]);
    assert_ne!(
        reminted.cell(),
        editor.card().cell(),
        "the re-minted authored card is a fresh portable cell"
    );

    println!("deos.editor.* authored a card live from JS: view + field + affordance, cap-gated, refused over-reach in-band.");
}
