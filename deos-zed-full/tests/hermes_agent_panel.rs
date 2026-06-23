//! THE CONFINED-HERMES AGENT PANEL, DOCKED + DRIVEN IN A REAL ZED WORKSPACE.
//!
//! This is the DONE bar for "wire the confined Hermes agent into the full Zed
//! Workspace embed as a working AGENT PANEL". Where `full_workspace_over_cells.rs`
//! proves the project/outline/terminal panels dock + run over the cell-ledger,
//! THIS proves the agent panel does too — and that it is LIVE, not a snapshot:
//!
//!   * a REAL [`workspace::Workspace`] (over a [`FirmamentZedFs`] cell-ledger);
//!   * the [`HermesPanel`] — a [`workspace::Panel`] wrapping deos-hermes's live
//!     [`AgentDockView`] over a real, persistent [`HermesGateway`] (an embedded
//!     cipherclerk + the verified Lean executor) — `add_panel`'d into the dock;
//!   * the panel RESOLVES back out by type (`workspace.panel::<HermesPanel>()` is
//!     `Some`) alongside the project/outline/terminal panels;
//!   * driving a MULTI-TURN agent session through the panel's real gateway fires
//!     genuine cap-gated, metered, receipted turns visible in the panel's ledger;
//!     the budget DEPLETES turn-over-turn; an OUT-OF-MANDATE call is REFUSED
//!     in-band (the same dev-loop `agent_loop_acceptance` proves, now a Workspace
//!     panel).
//!
//! The agent's *brain* is the faithful in-process ACP peer (the live model is
//! environment-blocked, per deos-hermes's honest scope); the gate, the verified
//! executor, the receipts, and the ACP wire are all REAL.
//!
//! Only compiled under `--features full-zed`.
#![cfg(feature = "full-zed")]

use std::sync::{Arc, RwLock};

use fs::Fs;
use gpui::{TestAppContext, VisualTestContext};
use project::Project;
use settings::SettingsStore;
use workspace::{MultiWorkspace, Workspace};

use deos_hermes::cockpit_surface::{AgentDockView, HermesSession};
use deos_hermes::surface::{AgentDockModel, RefusalLeg};
use deos_hermes::{AgentCipherclerk, AgentRuntime, GrantRegistry, HermesGateway, HeldToken};

use deos_zed_full::hermes_panel::{add_hermes_panel, HermesPanel};
use deos_zed_full::{boot, FirmamentZedFs};

/// Build a TIGHTLY-confined gateway for the panel's session, in the spirit of the
/// `agent_loop_acceptance` test's confinement — `terminal` tightened to rate 3 (so
/// the session can EXHAUST it and we witness a fail-closed rate refusal in the
/// panel), and `write_file` DENIED entirely (rate 0 — the out-of-mandate tool,
/// refused fail-closed on its first attempt). We deny `write_file` (not
/// `image_generate`) because the in-process scripted brain DOES reach for it on a
/// "write a note" prompt, so the denial is exercised end-to-end through the panel.
/// The session mandate expires at height 1000. Returns a `'static` gateway (the
/// runtime is leaked, exactly as the live dock holds it).
fn confined_gateway() -> HermesGateway<'static> {
    let mut cclerk = AgentCipherclerk::new();
    let root: HeldToken = cclerk.mint_token(&[7u8; 32], "deos");
    let rt: &'static AgentRuntime =
        Box::leak(Box::new(AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos")));
    let registry = GrantRegistry::default_for_session(1000)
        .with_standard_tool_grants(1000)
        .with_tool_grant("terminal", 3, 1000)
        .with_grant_for_tool_deny("write_file");
    HermesGateway::new(rt, root, registry)
}

/// Drive ONE prompt through the panel's live view (folding the whole turn
/// deterministically via `drain_all`, no timer pacing) and return the panel's
/// rendered model afterward. This exercises the EXACT path the interactive dock
/// runs on a keypress: `AgentDockView::submit` (drive the confined session → the
/// gate → buffer the deltas) then drain into the model the panel paints.
fn drive_prompt(
    view: &gpui::Entity<AgentDockView>,
    vcx: &mut VisualTestContext,
    prompt: &str,
) -> AgentDockModel {
    view.update(vcx, |v, cx| {
        v.submit(prompt, cx);
        v.drain_all(cx);
        v.model().clone()
    })
}

#[gpui::test]
async fn confined_hermes_agent_panel_docks_and_runs_in_the_workspace(cx: &mut TestAppContext) {
    // 1. The Workspace + panel globals (settings store, theme, the editor/panel
    //    crate registrations) — the deos subset of the standalone binary's init.
    cx.update(|cx| {
        let settings_store = SettingsStore::test(cx);
        cx.set_global(settings_store);
        boot::install_workspace_globals(cx);
    });
    cx.executor().allow_parking();

    // 2. A cell-ledger filesystem with a seeded project, and a REAL Zed Project +
    //    Workspace over it (the same construction the full-workspace proof uses).
    let fzfs = Arc::new(FirmamentZedFs::new());
    fzfs.seed_file("/proj/main.rs", "fn main() {}\n").unwrap();
    let fs: Arc<dyn Fs> = fzfs.clone();
    let project = Project::test(fs.clone(), ["/proj".as_ref()], cx).await;
    let window = cx.add_window(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
    let workspace = window.read_with(cx, |mw, _| mw.workspace().clone()).unwrap();
    let vcx = &mut VisualTestContext::from_window(window.into(), cx);

    // 3. DOCK THE REAL PROJECT/OUTLINE/TERMINAL PANELS (so the agent panel docks
    //    ALONGSIDE them, exactly as in the real embedded IDE).
    let weak_ws = workspace.downgrade();
    let panels_task = vcx.update(|window, cx| {
        let weak_ws = weak_ws.clone();
        window.spawn(cx, async move |cx| {
            boot::load_firmament_panels(weak_ws, cx.clone()).await
        })
    });
    vcx.run_until_parked();
    let _ = panels_task
        .await
        .expect("the project/outline/terminal panels load into the dock");

    // 4. DOCK THE CONFINED-HERMES AGENT PANEL over a tightly-confined, persistent
    //    gateway (the real cipherclerk + verified executor). `HermesSession::with_gateway`
    //    starts the session clock at 100 (the deadline leg lands later when we
    //    place a prompt past height 1000).
    let session = HermesSession::with_gateway("sess-panel", confined_gateway(), 100);
    let panel = workspace.update_in(vcx, |ws, window, cx| {
        add_hermes_panel(ws, session, "sess-panel", window, cx)
    });
    vcx.run_until_parked();

    // 5. THE AGENT PANEL IS PRESENT IN THE WORKSPACE — resolve it back out of the
    //    real dock BY TYPE. The workspace's own panel registry answers — alongside
    //    the project/outline/terminal panels, all live citizens of the same dock.
    workspace.read_with(vcx, |ws, cx| {
        assert!(
            ws.panel::<HermesPanel>(cx).is_some(),
            "the confined-Hermes agent panel is mounted + resolvable in the dock"
        );
        assert!(
            ws.panel::<project_panel::ProjectPanel>(cx).is_some(),
            "the project panel is still docked alongside the agent panel"
        );
        assert!(
            ws.panel::<terminal_view::terminal_panel::TerminalPanel>(cx).is_some(),
            "the terminal panel is still docked alongside the agent panel"
        );
    });
    // The resolved panel is the same entity we added, and it reports itself as the
    // agent surface.
    let resolved = workspace
        .read_with(vcx, |ws, cx| ws.panel::<HermesPanel>(cx))
        .expect("the agent panel resolves");
    assert_eq!(resolved.entity_id(), panel.entity_id(), "same panel entity");

    let view = panel.read_with(vcx, |p, _| p.view().clone());

    // ════ TURN 1 — three in-mandate calls: a search + two builds. Each is a real
    //     cap-gated, metered, RECEIPTED turn the panel's ledger shows. ════
    let m1 = drive_prompt(&view, vcx, "search for dregg, then build and test it");
    // The agent reached for: web_search (Fetch floor) + terminal(build) + terminal(test).
    assert_eq!(m1.tool_lines.len(), 3, "three gated tool-calls in turn 1: {m1:?}");
    assert!(
        m1.tool_lines.iter().all(|l| l.allowed),
        "all three turn-1 calls were ADMITTED (in-mandate): {:?}",
        m1.tool_lines
    );
    // Each allow carries a REAL receipt (a hex turn hash from the verified executor).
    for line in m1.tool_lines.iter().filter(|l| l.allowed) {
        assert!(
            line.detail.starts_with("receipt "),
            "an admitted call leaves a real receipt: {line:?}"
        );
    }
    // The terminal mandate (rate 3) is now 2 spent / 1 remaining — the budget bar
    // the panel paints has depleted.
    let term_row = m1
        .mandate_rows
        .iter()
        .find(|r| r.label.contains("terminal"))
        .expect("the terminal mandate row is visible in the panel's budget view");
    assert_eq!(term_row.spent, 2, "two terminal calls spent after turn 1");
    assert_eq!(term_row.remaining(), 1, "rate-3 terminal: one call left after turn 1");

    // ════ TURN 2 — same persistent gateway: one MORE build (the last allowed),
    //     then a second build that EXHAUSTS the terminal rate and is REFUSED. ════
    // The model's `tool_lines` is the FLAT, session-wide ledger (it accumulates
    // across turns); the calls THIS turn added are the tail past turn 1's three.
    let m2 = drive_prompt(&view, vcx, "build once more, then build again");
    let turn2 = &m2.tool_lines[3..];
    assert_eq!(turn2.len(), 2, "two gated tool-calls in turn 2: {turn2:?}");
    // The first build is admitted (3rd allowed terminal); the second is refused.
    assert!(turn2[0].allowed, "the 3rd terminal call is the last allowed");
    assert!(
        !turn2[1].allowed,
        "the 4th terminal call is over rate — REFUSED in-band"
    );
    // The permission moment names the RATE leg (the panel surfaces this prominently).
    let pm = m2
        .last_permission
        .as_ref()
        .expect("a permission moment after turn 2");
    assert!(!pm.allowed, "the most-recent decision is a refusal");
    assert_eq!(pm.leg, Some(RefusalLeg::Rate), "the refusal names the rate leg");
    assert!(
        pm.detail.contains("rate exhausted"),
        "the refusal reason names the rate leg: {}",
        pm.detail
    );
    // THE CUMULATIVE BUDGET is now fully depleted: across both turns the rate-3
    // terminal mandate sits at its ceiling. The model's per-turn `mandate_rows`
    // animate one turn's spend; the SESSION's mandate reads the gateway's
    // cumulative counters (the real session-wide budget) — query it through the
    // panel's live view to assert the whole-session depletion.
    let cum = view.read_with(vcx, |v, _| v.session().mandate());
    let term_cum = cum
        .rows
        .iter()
        .find(|r| matches!(r.key, deos_hermes::MandateKey::Tool(ref t) if t == "terminal"))
        .expect("the terminal mandate row in the cumulative session view");
    assert_eq!(term_cum.calls_made, 3, "terminal at its cumulative rate-3 ceiling");
    assert_eq!(term_cum.remaining, 0, "terminal budget fully depleted across the session");

    // ════ TURN 3 — the OUT-OF-MANDATE tool: `write_file` is denied entirely
    //     (rate 0). The agent reaches for it on a "write a note" prompt; its FIRST
    //     attempt fails closed — refused in-band. ════
    let m3 = drive_prompt(&view, vcx, "write a note to plan.md");
    let wf = m3
        .tool_lines
        .iter()
        .find(|l| l.name == "write_file")
        .expect("the agent reached for write_file");
    assert!(
        !wf.allowed,
        "the out-of-mandate write_file is REFUSED on its first attempt (fail-closed): {wf:?}"
    );
    // It never ran — the denied tool's cumulative counter stays at 0 (fail-closed).
    let cum = view.read_with(vcx, |v, _| v.session().mandate());
    let wf_cum = cum
        .rows
        .iter()
        .find(|r| matches!(r.key, deos_hermes::MandateKey::Tool(ref t) if t == "write_file"))
        .expect("the write_file deny row in the cumulative session view");
    assert_eq!(wf_cum.calls_made, 0, "the denied write_file never advanced its counter");

    // THE WHOLE-PANEL INVARIANT: the panel resolved, docked alongside the IDE
    // panels, and drove a real multi-turn receipted session — admits leaving
    // receipts, a depleting budget, and in-band refusals (rate + whole-tool deny) —
    // all surfaced in the live model the dock paints.
    assert!(
        m3.transcript.len() >= 6,
        "the multi-turn conversation accumulated across the three prompts: {} entries",
        m3.transcript.len()
    );

    // Keep the workspace handle live to the end.
    let _: &gpui::Entity<Workspace> = &workspace;
}
