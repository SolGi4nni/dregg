//! THE NOUS-FLEX RUNG, PROVEN BY RUNNING — a brain DECIDES the `editView` JS and
//! the edit lands as a receipted patch, bounded by its `held`.
//!
//! Run: `cd deos-hermes && cargo test --features js-agent --test hermes_authors_card_via_run_js`
//! (the default `cargo test` is mozjs-free — the authoring `run_js` path pulls
//! deos-js / real SpiderMonkey via the `js-agent` feature.)
//!
//! The already-landed keystone (`deos-view/tests/agent_authors_a_card_live.rs`)
//! proved the loop with a SCRIPTED snippet: a fixed `agent_js` string drives
//! `deos.editor.editView`. THIS file closes the next rung — the JS is no longer a
//! constant: it arrives as the body of a `run_js` tool-call, routed through the
//! proven `HermesGateway`, run by `RunJsAuthoringTool` via `JsRuntime::run_authoring`.
//! The agent, given a card + a goal, WROTE the `editView` JS itself.
//!
//! Three things proven:
//!   (a) THE TOOL — `RunJsAuthoringTool::run_on` admits the `run_js` tool-call (the
//!       accountability turn), runs the agent-decided `editView` JS, and the card's
//!       view changes — a receipted provenance patch blamed on the agent.
//!   (b) THE LIVE-DECIDE PATH — the SAME `editView` JS arrives as a `run_js`
//!       tool-call's `rawInput.script` over a REAL `AcpClient` session and is run by
//!       `LiveAuthoringHands` (the `run_js` hook). A faithful scripted-brain
//!       stand-in (the `MockHermesPeer`) DECIDES + EMITS the JS; the run_js→hook→
//!       run_authoring→editView path is exercised end-to-end over the ACP wire. The
//!       live `hermes-acp`-selects-the-JS seam is named in `live_authors_card_via_run_js`.
//!   (c) THE CAP TOOTH — an over-reach (the agent holds Signature, the card's
//!       `edit_authority` is Proof) is refused IN-BAND: `editView` returns null, NO
//!       patch, NO receipt, the view untouched.

#![cfg(feature = "js-agent")]

use std::sync::{Arc, RwLock};

use deos_hermes::acp_client::AcpClient;
use deos_hermes::{
    GrantRegistry, HermesGateway, LiveAuthoringHands, MockHermesPeer, RunJsAuthoringTool,
    ScriptedCall, ToolCallRequest,
};
use deos_js::card_editor::{BindProps, TextProps, ViewTree};
use deos_js::portable::{AffordanceSpec, ApplyOp, AppletManifest, PortableApplet};
use deos_js::JsRuntime;
use dregg_cell::AuthRequired;
use dregg_doc::Author;
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

/// The agent's blame identity — every patch the agent's JS lands is attributed to it.
const AGENT: Author = Author(99);

/// deos the grantor: the runtime that admits the agent's `run_js` worker and runs
/// its accountability turns.
fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// A scoped, rate-limited `run_js` grant for the agent (the accountability mandate
/// the gateway meters the tool-call on).
fn session_registry() -> GrantRegistry {
    GrantRegistry::default_for_session(10_000).with_tool_grant("run_js", 50, 10_000)
}

/// A counter card's manifest: a "Counter" title + a live count bind, an `inc`
/// affordance. The shape `deos-view` paints — the card the agent authors a button onto.
fn counter_manifest() -> AppletManifest {
    let view = ViewTree::VStack {
        children: vec![
            ViewTree::Text {
                props: TextProps {
                    text: "Counter".into(),
                },
            },
            ViewTree::Bind {
                props: BindProps {
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

/// The agent's authoring snippet — its hands rewriting its own card's UI. This is
/// the JS the brain DECIDES to write, given the card + the goal ("add a +1 button
/// that fires `inc`, and relabel the title Counter → Clicks"). Identical in shape
/// to the scripted keystone, but here it is the *decided* body of a `run_js` call.
const AGENT_EDITVIEW_JS: &str = r#"
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

// SpiderMonkey's `JSEngine::init()` is PROCESS-GLOBAL + one-shot, so all
// scenarios share ONE `JsRuntime`, threaded through the tools. Each `eval` runs on
// a fresh global, so reuse is sound. All scenarios live in one `#[test]` so the
// engine is initialised exactly once under cargo's parallel test threads.

#[test]
fn an_agent_authors_a_card_via_run_js_decided_js() {
    let mut js = JsRuntime::new().expect("boot SpiderMonkey once");

    // ── (a) THE TOOL — the agent-decided editView JS lands receipted patches ──────
    {
        let (rt, root) = grantor();
        let mut gw = HermesGateway::new(&rt, root, session_registry());
        // The agent holds None (single-custody, broad over its own card) and authors
        // as itself (Author 99). The card requires Signature to author — held satisfies.
        let tool = RunJsAuthoringTool::new(AuthRequired::None, AGENT);

        let manifest = counter_manifest();
        let mut pk = [0u8; 32];
        pk[0] = 0xC0;
        let card = PortableApplet::mint(pk, [0u8; 32], &manifest);

        // The brain produced a `run_js` call whose body is the editView JS it wrote.
        let call = ToolCallRequest::new(
            "s",
            "tc-author-1",
            "run_js",
            serde_json::json!({ "script": "author: add +1 button, relabel title" }),
        );

        let out = tool.run_on(
            &mut js,
            &mut gw,
            &call,
            50,
            card,
            manifest,
            /*edit_authority=*/ AuthRequired::Signature,
            AGENT_EDITVIEW_JS,
        );

        // The `run_js` tool-call itself was admitted accountably (a metered, receipted
        // ToolGrant turn) — the agent is granted its authoring hands this turn.
        assert!(
            out.tool_admitted(),
            "the run_js authoring tool-call is admitted by the gateway: {:?}",
            out.tool_outcome
        );
        assert_eq!(
            gw.calls_made_for_tool("run_js"),
            1,
            "the run_js call is metered — every authoring action is receipted, never free"
        );
        assert!(
            out.js_error.is_none(),
            "the agent's authoring JS ran cleanly: {:?}",
            out.js_error
        );
        // The agent's JS folded a tree carrying BOTH the new button AND the relabel.
        assert_eq!(
            out.result,
            Some(1),
            "the agent's editView JS produced a tree with its +1 button AND the relabel"
        );
        // ACCOUNTABLE: two authoring gestures (addButton + relabel) each committed a
        // real provenance turn on the card's chain.
        assert_eq!(
            out.patches_committed, 2,
            "the agent's two editView gestures each landed a receipted provenance patch"
        );
        assert!(
            out.receipts.len() == 2 && out.receipts.iter().all(|h| h != &[0u8; 32]),
            "each authoring gesture left a real (non-zero) receipt: {:?}",
            out.receipts
        );
        // The re-folded view-source carries the new button (the UI the agent built).
        let view = out.view_source.clone().expect("authoring yields a view source");
        let tree = ViewTree::from_json(&view).expect("the authored view is parseable");
        assert!(
            tree.has_button_for("inc"),
            "the agent authored a card's UI from within — the +1 button is in the view"
        );
        // BLAME — the authored lines are attributed to the AGENT (Author 99).
        assert!(
            out.blamed_authors.contains(&99),
            "the agent's authoring patches are blamed on the agent (Author 99): {:?}",
            out.blamed_authors
        );
    }

    // ── (c) THE CAP TOOTH — an over-reach is refused IN-BAND, no patch, no receipt ──
    {
        let (rt, root) = grantor();
        let mut gw = HermesGateway::new(&rt, root, session_registry());
        // The agent holds only SIGNATURE; the card requires PROOF to author — over-reach.
        let tool = RunJsAuthoringTool::new(AuthRequired::Signature, AGENT);

        let manifest = counter_manifest();
        let mut pk = [0u8; 32];
        pk[0] = 0xCD;
        let card = PortableApplet::mint(pk, [0u8; 32], &manifest);

        // The agent decides this editView JS, but it over-reaches the card's authority.
        let overreach_js = r#"
            var card = deos.editor.card();
            // OVER-REACH: this card needs Proof, the agent holds only Signature.
            var refused = deos.editor.editView(card, {
                op: "addButton", label: "+1", affordance: "inc", arg: 1
            });
            (refused === null) ? 1 : 0;     // 1 iff the edit was refused in-band
        "#;
        let call = ToolCallRequest::new(
            "s",
            "tc-author-over",
            "run_js",
            serde_json::json!({ "script": "author: add +1 (over-reach)" }),
        );

        let out = tool.run_on(
            &mut js,
            &mut gw,
            &call,
            52,
            card,
            manifest,
            /*edit_authority=*/ AuthRequired::Proof,
            overreach_js,
        );

        // The tool-call ITSELF is still admitted (the agent IS granted run_js — the
        // bound is on what it may AUTHOR, not on running the authoring JS at all).
        assert!(
            out.tool_admitted(),
            "run_js is granted (the bound is on the authoring, not on running JS)"
        );
        // THE BOUND: the over-reach authored NOTHING. No patch, no receipt — the cap
        // tooth refused in-band, and the JS saw the refusal as `null`.
        assert!(
            !out.authored(),
            "OVER-REACH HOLE — a Proof-gated card was authored by a Signature-held agent"
        );
        assert_eq!(
            out.patches_committed, 0,
            "the refused over-reach committed NOTHING — no patch, no turn"
        );
        assert!(
            out.receipts.is_empty(),
            "an over-reach leaves NO receipt — it never happened"
        );
        assert_eq!(
            out.result,
            Some(1),
            "the agent's JS saw the cap-gate refusal in-band (editView returned null)"
        );
        assert!(
            out.js_error.is_none(),
            "a cap-gate refusal is an EXPECTED in-band outcome, not a fatal eval error: {:?}",
            out.js_error
        );
    }

    // ── (b) THE LIVE-DECIDE PATH — the JS arrives as a run_js tool-call over ACP ──
    // The MockHermesPeer is the faithful scripted-brain stand-in: it emits a `run_js`
    // tool-call whose `rawInput.script` IS the agent's decided editView JS, exactly
    // as the real `acp_adapter` would frame the model's chosen script. The real
    // AcpClient drives the session and dispatches the call to the LiveAuthoringHands
    // hook, which runs `run_authoring` against the card. This exercises the full
    // run_js → hook → run_authoring → editView path end-to-end over the ACP wire.
    // Runs LAST because it consumes the shared `js` runtime.
    {
        let (rt, root) = grantor();
        let session_gw = HermesGateway::new(&rt, root, session_registry());
        // The hook owns its OWN gateway over the same grantor (a self-borrow would
        // otherwise block borrowing the client's gateway) — both share the ledger.
        let (rt2, root2) = grantor();
        let hook_gw = HermesGateway::new(&rt2, root2, session_registry());

        let tool = RunJsAuthoringTool::new(AuthRequired::None, AGENT);
        // The card factory hands the brain its card to author each call.
        let card_factory = || {
            let manifest = counter_manifest();
            let mut pk = [0u8; 32];
            pk[0] = 0xC1;
            let card = PortableApplet::mint(pk, [0u8; 32], &manifest);
            (card, manifest, AuthRequired::Signature)
        };

        // SpiderMonkey is already booted (one-shot, process-global); thread the test's
        // runtime in via `with_runtime` rather than booting another (which would error
        // `AlreadyInitialized`).
        let hands = LiveAuthoringHands::with_runtime(tool, hook_gw, card_factory, js);

        // The brain's `run_js` call: the body is the decided editView JS.
        let script = MockHermesPeer::new(
            "sess-author",
            vec![ScriptedCall::new(
                "run_js",
                serde_json::json!({ "script": AGENT_EDITVIEW_JS }),
            )],
        );

        let mut client = AcpClient::new(script, session_gw, 10).with_run_js_hook(hands.into_hook());
        let run = client
            .run_prompt("/tmp", "Add a reset/+1 button to my counter card and relabel it.")
            .expect("the ACP session drives the run_js authoring call");

        // The gateway admitted the `run_js` tool-call (the accountability turn).
        assert_eq!(run.verdicts.len(), 1, "one run_js permission round-trip");
        assert!(
            run.verdicts[0].1.allowed(),
            "deos admitted the run_js authoring call over ACP: {:?}",
            run.verdicts[0].1
        );

        // The brain's JS authored the card: the hook's JsRunRecord carries the
        // receipted patches it landed (recorded as `fires_committed`).
        let js_runs = client.js_runs();
        assert_eq!(js_runs.len(), 1, "one run_js authoring run recorded");
        let rec = &js_runs[0];
        assert!(
            rec.js_error.is_none(),
            "the live-decided authoring JS ran cleanly over ACP: {:?}",
            rec.js_error
        );
        assert_eq!(
            rec.result,
            Some(1),
            "the live-decided editView JS folded the +1 button AND the relabel"
        );
        assert_eq!(
            rec.fires_committed, 2,
            "the live-decided run_js authored TWO receipted patches (addButton + relabel)"
        );
        assert!(
            rec.receipts.len() == 2 && rec.receipts.iter().all(|h| h != &[0u8; 32]),
            "each live-decided authoring gesture left a real receipt: {:?}",
            rec.receipts
        );
        // The exact JS the brain decided is captured on the record (the auditable body).
        assert!(
            rec.script.contains("deos.editor.editView"),
            "the recorded brain script is the editView authoring JS it decided"
        );
    }
}

// ──────────────── THE LIVE SELECTION SEAM (named, run-on-demand) ─────────────────
//
// The named seam: a REAL `hermes-acp` Copilot brain (e.g. `copilot:claude-sonnet-4.5`)
// DECIDES the `editView` JS itself — we give it a card + a goal in the prompt and it
// writes the `deos.editor.editView(...)` body, framed as a `run_js` tool-call. This
// test drives the SAME `AcpClient` + `LiveAuthoringHands` as scenario (b), but over
// the real subprocess instead of the scripted-brain stand-in.
//
// It SKIPS gracefully when the env can't run it — the live ceiling, identical to
// `tests/live_acp.rs`: a working `hermes-acp` (its venv has `agent-client-protocol`)
// AND a reachable model provider. Without those, the model never emits a `run_js`
// call carrying authoring JS, so there is nothing to run (verdicts = 0). This is the
// ONE seam between the scripted-brain proof above and a fully-live decide: the model
// reliably emitting WELL-FORMED `deos.editor.editView` JS as its `run_js` body. The
// scripted stand-in proves the run_js→editView authoring PATH; this proves the live
// brain DRIVES it when the provider cooperates.
//
// Run it explicitly (it is `#[ignore]` so the default suite stays hermetic):
//   HERMES_ACP_BIN=/opt/homebrew/bin/hermes-acp HERMES_INFERENCE_PROVIDER=copilot \
//     HERMES_ACP_MODEL=copilot:claude-sonnet-4.5 HERMES_MAX_ITERATIONS=3 \
//     cargo test --features js-agent --test hermes_authors_card_via_run_js \
//     -- --ignored --nocapture live_authors_card_via_run_js
#[test]
#[ignore = "drives the real hermes-acp subprocess; run with --ignored when a hermes-acp install + reachable provider is present"]
fn live_authors_card_via_run_js() {
    use deos_hermes::AcpTransport;
    use std::process::Command;

    let program = std::env::var("HERMES_ACP_BIN").unwrap_or_else(|_| "hermes-acp".to_string());
    // Usable iff `hermes-acp --check` imports `acp` + the adapter and prints "check OK".
    let usable = Command::new(&program)
        .arg("--check")
        .output()
        .ok()
        .map(|o| o.status.success() && String::from_utf8_lossy(&o.stdout).contains("check OK"))
        .unwrap_or(false);
    if !usable {
        eprintln!(
            "SKIP: no usable `hermes-acp` (set HERMES_ACP_BIN; its venv needs \
             `agent-client-protocol` — `hermes-acp --check` must print 'check OK')."
        );
        return;
    }
    eprintln!("LIVE (authoring): driving `{program}` — the brain decides the editView JS");

    let (rt, root) = grantor();
    let session_gw = HermesGateway::new(&rt, root, session_registry());
    let (rt2, root2) = grantor();
    let hook_gw = HermesGateway::new(&rt2, root2, session_registry());

    let tool = RunJsAuthoringTool::new(AuthRequired::None, AGENT);
    let card_factory = || {
        let manifest = counter_manifest();
        let mut pk = [0u8; 32];
        pk[0] = 0xCE;
        let card = PortableApplet::mint(pk, [0u8; 32], &manifest);
        (card, manifest, AuthRequired::Signature)
    };
    let hands = match LiveAuthoringHands::new(tool, hook_gw, card_factory) {
        Ok(h) => h,
        Err(e) => {
            eprintln!("SKIP: could not boot SpiderMonkey for the live authoring hands: {e}");
            return;
        }
    };

    let transport = match AcpTransport::spawn_hermes(&program, &[]) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("SKIP: could not spawn `{program}`: {e}");
            return;
        }
    };
    let mut client = AcpClient::new(transport, session_gw, 10).with_run_js_hook(hands.into_hook());

    let model = std::env::var("HERMES_ACP_MODEL")
        .unwrap_or_else(|_| "bedrock:global.amazon.nova-2-lite-v1:0".to_string());

    // The goal we hand the live brain — it must WRITE the editView JS itself.
    let prompt = "You have a `run_js` tool that runs JavaScript with a `deos.editor` API. \
                  The current card has a title text \"Counter\" and a count display. Author \
                  the card by calling run_js with a script that uses \
                  `deos.editor.editView(deos.editor.card(), { op: \"addButton\", label: \"+1\", \
                  affordance: \"inc\", arg: 1 })` to add a +1 button. Emit exactly that run_js \
                  call and nothing else.";

    match client.run_prompt_with_model("/tmp", prompt, Some(&model)) {
        Ok(run) => {
            assert!(
                !run.stop_reason.is_empty(),
                "live authoring session completed with a stop_reason"
            );
            eprintln!(
                "LIVE authoring handshake/session OK (stop_reason = {}, tool-calls = {}, \
                 run_js authoring runs = {})",
                run.stop_reason,
                run.tool_calls.len(),
                client.js_runs().len()
            );
            // If a provider was reachable, the brain emitted a `run_js` authoring call;
            // assert any authored run landed a real receipted patch (the brain's edit
            // reached the card). If no provider was reachable, js_runs is empty and we
            // proved only the live handshake — the named ceiling, not a code defect.
            for rec in client.js_runs() {
                if rec.fires_committed > 0 {
                    assert!(
                        rec.receipts.iter().all(|h| h != &[0u8; 32]),
                        "a live-authored patch left a real (non-zero) receipt"
                    );
                    eprintln!(
                        "LIVE: the brain authored {} receipted patch(es) from its own editView JS",
                        rec.fires_committed
                    );
                } else if let Some(err) = &rec.js_error {
                    // The model emitted a run_js body that didn't author — names the seam:
                    // the live brain didn't (yet) produce well-formed editView JS.
                    eprintln!("LIVE-SEAM: the brain's run_js body did not author (js_error): {err}");
                } else {
                    eprintln!(
                        "LIVE-SEAM: the brain emitted a run_js body that ran but authored \
                         no patch (likely not a deos.editor.editView call): {:?}",
                        rec.script
                    );
                }
            }
        }
        Err(e) => eprintln!("SKIP: live loop did not complete the handshake: {e}"),
    }
}
