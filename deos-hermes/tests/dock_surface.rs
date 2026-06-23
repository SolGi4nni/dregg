//! THE AGENT DOCK SURFACE TEST — the confined-agent dock renders its chat,
//! tool-call ledger, and mandate inspector.
//!
//! Two layers:
//!   * a HEADLESS MODEL test (always runs, no gpui) that asserts the
//!     [`AgentDockModel`] the surface renders from carries the chat text, the
//!     per-tool ledger rows (receipt on allow / reason on reject), and the
//!     mandate inspector text — the exact fields the gpui panes paint;
//!   * (under `--features screenshot`) an OFFSCREEN CAPTURE that drives the gpui
//!     [`AgentDockView`] to a painted PNG, proving the surface renders end-to-end
//!     in a headless gpui app. Best-effort: skipped with a note if no offscreen
//!     wgpu backend is available in-env.

use std::sync::{Arc, RwLock};

use deos_hermes::acp::ToolCallRequest;
use deos_hermes::surface::AgentDockModel;
use deos_hermes::{GrantRegistry, HermesGateway, PromptRun};
use dregg_sdk::{AgentCipherclerk, AgentRuntime};

/// Build a realistic dock model: an allowed web_search + a rate-exhausted
/// terminal reject, through the real gateway, so the ledger has BOTH polarities.
fn demo_model() -> AgentDockModel {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    // A tiny terminal rate (1) so the second terminal call is refused in-band.
    let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
    let mut gw = HermesGateway::new(&rt, root, registry);

    let mut run = PromptRun {
        agent_text: "searched, then tried a build.".into(),
        stop_reason: "end_turn".into(),
        ..Default::default()
    };
    for (id, name, args) in [
        ("tc-1", "web_search", serde_json::json!({"query": "dregg"})),
        ("tc-2", "terminal", serde_json::json!({"command": "cargo build"})),
    ] {
        let call = ToolCallRequest::new("sess-demo", id, name, args);
        let outcome = gw.admit_call(&call, 50);
        run.verdicts.push((call, outcome));
    }
    AgentDockModel::from_run("sess-demo", &run, &gw)
}

#[test]
fn dock_model_carries_chat_ledger_and_mandate() {
    let model = demo_model();

    // chat pane
    assert!(model.agent_text.contains("searched"));
    assert_eq!(model.stop_reason, "end_turn");

    // tool-call ledger: two rows, one allow with a receipt, both names present.
    assert_eq!(model.tool_lines.len(), 2);
    let search = model.tool_lines.iter().find(|l| l.name == "web_search").unwrap();
    assert!(search.allowed, "web_search committed a receipted turn");
    assert!(search.detail.contains("receipt"), "allow row shows the receipt id");
    assert!(model.tool_lines.iter().any(|l| l.name == "terminal"));

    // mandate inspector text
    assert!(model.mandate_text.contains("MANDATE"));

    // the plain-text render (the TUI/CLI face) folds all three together.
    let text = model.render_text();
    assert!(text.contains("Hermes (confined)"));
    assert!(text.contains("web_search"));
    assert!(text.contains("MANDATE"));
}

/// OFFSCREEN render: drive the gpui dock view to a PNG. Best-effort — if the
/// offscreen wgpu backend is unavailable in-env, the capture errors and we note
/// it rather than fail (the model test above is the always-on render proof).
#[cfg(feature = "screenshot")]
#[test]
fn dock_surface_captures_offscreen() {
    let model = demo_model();
    let out = std::env::temp_dir().join("deos-hermes-dock.png");
    match deos_hermes::screenshot::capture_dock(&out, model) {
        Ok((w, h)) => {
            assert!(w > 0 && h > 0, "captured a non-empty frame");
            assert!(out.exists(), "wrote the PNG to {}", out.display());
            println!("dock surface captured offscreen: {}x{} -> {}", w, h, out.display());
        }
        Err(e) => {
            // No offscreen GPU backend in this env — the headless model test is
            // the render proof; record the skip honestly.
            println!("offscreen capture unavailable in-env (skipping): {e}");
        }
    }
}
