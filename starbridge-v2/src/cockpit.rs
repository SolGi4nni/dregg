//! The gpui cockpit — the comprehensive visual master interface.
//!
//! This is the visual layer (gpui-gated, `native-full` only). It renders the
//! embedded [`World`](crate::world::World) — the live local dregg image — across
//! the four dregg-surpasses-Smalltalk axes, each a panel:
//!
//!   * CELL WORLD (left rail) — every cell as a live object; click to inspect.
//!     The ocap axis: the cap count + the graph edges are first-class.
//!   * INSPECTOR (center) — the selected object reflected through the uniform
//!     [`reflect`](crate::reflect) model: cell ⟷ receipt ⟷ image, navigable.
//!   * BLOCKLACE (center-low) — the provenance axis: the receipt chain as a
//!     navigable causal history (time-travel).
//!   * COMPOSER (right) — direct-manipulation turn composition: pick a verb,
//!     watch the EMBEDDED EXECUTOR run it and the image + receipts update live.
//!   * DYNAMICS (right-low) — the live activity feed off the dynamics stream.
//!   * IMAGE/FEDERATION (rail header) — the distribution axis: this image's
//!     state-root commitment, presented as one sovereign image among a
//!     federation.
//!
//! gpui is single-threaded; the `World` is shared as `Rc<RefCell<World>>`. Every
//! verb button mutates it through `World::commit_turn` (the REAL executor) and
//! the views re-render from the post-state on the next frame.

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, prelude::*, px, Context, FocusHandle, Hsla, IntoElement, KeyDownEvent, MouseButton,
    ParentElement, Render, SharedString, Styled, Window,
};

use dregg_cell::CellId;

use crate::views::{pill, section_title, theme};
use starbridge_v2::dynamics;
use starbridge_v2::palette::{Category, CommandId, CommandPalette};
use starbridge_v2::reflect::{self, Field, FieldValue, Inspectable, ObjectKind};
use starbridge_v2::shell::{Scene, Shell};
use starbridge_v2::surface::{SurfaceCapability, SurfaceId};
use starbridge_v2::world::{self, CommitOutcome, World};
// The feature panels — wired in as tabs of the master interface.
use starbridge_v2::{cipherclerk, debug, edit, replay};
// The A1 DEVELOPER content surfaces — the IDE's editor + terminal panes.
use starbridge_v2::buffer::{BufferCell, BufferView};
use starbridge_v2::terminal::{Command, TerminalCell, TerminalView};
// The A2 SWARM surface — multi-agent cap-coordinated swarm with notify edges.
use starbridge_v2::swarm::{Swarm, SwarmView};

/// Which object the inspector is focused on.
#[derive(Clone)]
pub enum Selection {
    Cell(CellId),
    Receipt(usize),
    Image,
}

/// Which workspace tab the right-hand pane presents. The master interface
/// surfaces the composer alongside the four feature panels.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Tab {
    Shell,
    Agent,
    /// The IDE's EDITOR pane — a text buffer as a cap-confined Surface cell
    /// (A1). Distinct from `Editor` (the artifact-authoring Live Editor).
    Buffer,
    /// The IDE's TERMINAL pane — a command surface as a cap-confined Surface
    /// cell (A1; the home of the ADOS tool-call seam).
    Terminal,
    Composer,
    Objects,
    Debugger,
    Replay,
    Cipherclerk,
    Editor,
    /// The A2 SWARM tab — multi-agent cap-coordinated activity surface.
    /// N agent panes as confined Surface cells, coordinating via the
    /// notify-edge inbox (EmitEvent → NotifyEdge → async drain turn).
    Swarm,
    /// The ORGANS tab — reflects each dregg organ's live cell-state (trustline /
    /// flash-well live in embed-core; channel / mailbox / court surfaced honestly
    /// as remote-path). See [`starbridge_v2::organs`].
    Organs,
    /// The GRAPH tab — the whole-graph ocap delegation layout (the View tree IS
    /// the ocap graph): nodes = cells, edges = capability grants, with multi-hop
    /// reachability + a layered delegation-depth layout. See
    /// [`starbridge_v2::graph`].
    Graph,
    /// The PROOFS tab — the proof-attach + STARK verification-status board: each
    /// committed turn's verification tier + the attach/verify route. See
    /// [`starbridge_v2::proofs`].
    Proofs,
}

impl Tab {
    const ALL: [Tab; 14] = [
        Tab::Shell,
        Tab::Agent,
        Tab::Swarm,
        Tab::Graph,
        Tab::Organs,
        Tab::Proofs,
        Tab::Buffer,
        Tab::Terminal,
        Tab::Composer,
        Tab::Objects,
        Tab::Debugger,
        Tab::Replay,
        Tab::Cipherclerk,
        Tab::Editor,
    ];
    fn label(self) -> &'static str {
        match self {
            Tab::Shell => "SHELL",
            Tab::Agent => "AGENT",
            Tab::Swarm => "SWARM",
            Tab::Graph => "GRAPH",
            Tab::Organs => "ORGANS",
            Tab::Proofs => "PROOFS",
            Tab::Buffer => "BUFFER",
            Tab::Terminal => "TERMINAL",
            Tab::Composer => "COMPOSER",
            Tab::Objects => "OBJECTS",
            Tab::Debugger => "DEBUGGER",
            Tab::Replay => "REPLAY",
            Tab::Cipherclerk => "CIPHERCLERK",
            Tab::Editor => "EDITOR",
        }
    }
}

/// The whole cockpit — owns the shared world + the current selection + a
/// dynamics cursor for the activity feed, plus the four feature panels' UI
/// state (the modules kept their renders gpui-free; the cockpit owns the state
/// and maps the render-models onto gpui).
pub struct Cockpit {
    world: Rc<RefCell<World>>,
    /// Stable, sorted list of cell ids (so the rail order is deterministic and
    /// selection survives across commits).
    cells: Vec<CellId>,
    selection: Selection,
    /// The last action's outcome banner (committed hash / rejection reason).
    last_outcome: Option<String>,
    /// Three anchor cells for the demo verbs (treasury, service, user).
    anchors: [CellId; 3],
    /// The active right-pane tab.
    tab: Tab,

    // --- DEBUGGER panel state ----------------------------------------------
    /// The turn the debugger inspects (a demo transfer the operator can run);
    /// re-executed faithfully via `debug::render` against the live world.
    debug_turn: dregg_turn::turn::Turn,
    /// The breakpoints the debugger evaluates over the turn's steps.
    breakpoints: Vec<debug::Breakpoint>,

    // --- REPLAY panel state ------------------------------------------------
    /// The time-travel scrubber cursor (a step in `0..=history.len()`).
    replay_cursor: usize,
    /// An optional pinned what-if fork (the cockpit owns it; `replay::Fork`).
    replay_fork: Option<replay::Fork>,

    // --- CIPHERCLERK panel state -------------------------------------------
    /// The HD-derived identity vault (real `AgentCipherclerk`s).
    clerk: cipherclerk::Cipherclerk,
    /// The last cipherclerk action's result banner (real mint/attenuate/
    /// delegate/discharge outcome).
    clerk_outcome: Option<cipherclerk::ClerkOutcome>,

    // --- EDITOR panel state ------------------------------------------------
    /// The live-editor's authoring/validation/deploy state.
    editor: edit::EditorState,

    // --- the cap-first SHELL / compositor ----------------------------------
    /// The cap-first window manager / compositor over the live world. Every
    /// window op routes through its CAP-GATED API.
    shell: Shell,
    /// The operator's cap-vault: the [`SurfaceCapability`] held for each open
    /// surface. The cockpit IS the operator (it holds every surface's cap), but
    /// it can ONLY drive a surface by presenting the cap from here — so the
    /// shell's ocap discipline is real, not bypassed. The console's cap lives
    /// here too (under `console_surface`).
    surface_caps: std::collections::HashMap<SurfaceId, SurfaceCapability>,
    /// The console surface's id (the privileged trusted-root surface).
    console_surface: SurfaceId,
    /// A monotonic frame-digest counter for the verified-scene present teaching
    /// moments (so every `present()` genuinely advances the frame).
    frame_seq: u64,

    // --- the AGENT-ACTIVITY surface (the ADOS keystone) --------------------
    /// The agent cell bound to the agent-activity surface — a cap-confined VIEW
    /// of an agent loop's provable activity (held mandate · cap-gated turns +
    /// receipts · authorization boundary), rendered as a Surface cell. The
    /// service cell stands in as a live, cap-holding, turn-committing agent.
    agent_surface: starbridge_v2::agent::AgentSurface,

    // --- the A1 EDITOR/BUFFER surface (a text buffer as a Surface cell) -----
    /// The editor buffer — a cap-confined text buffer backed by a real cell
    /// (its digest rides the cell's state; an edit is a cap-gated turn). The
    /// IDE's editor pane.
    editor_buffer: BufferCell,
    /// The WRITE capability the cockpit holds for `editor_buffer` (the shell
    /// minted it on open). The cockpit can only COMMIT an edit by presenting
    /// this — a read-only mirror could not (the §7 cap discipline at the editor).
    editor_buffer_cap: SurfaceCapability,

    // --- the A1 TERMINAL surface (a command surface as a Surface cell) ------
    /// The terminal — a cap-confined command surface whose backing cell's
    /// c-list IS the command authority (a command outside it REFUSES). The home
    /// of the ADOS A0 tool-call seam; the IDE's terminal pane.
    terminal: TerminalCell,

    // --- the A2 SWARM surface (multi-agent cap-coordination) ----------------
    /// The swarm coordinator: N agent cells coordinating as confined Surface
    /// cells with the notify-edge inbox (EmitEvent → NotifyEdge → drain turn).
    /// The treasury is the "coordinator" (holds caps to both service + user);
    /// service and user are the "workers" it orchestrates via emit-event.
    swarm: Swarm,

    // --- the ⌘K COMMAND PALETTE --------------------------------------------
    /// The command palette over EVERY action (open with ⌘K). The cockpit feeds
    /// it keystrokes and dispatches its selected `CommandId` through the same
    /// `&mut Cockpit` verbs the buttons call.
    palette: CommandPalette,
    /// Focus handle for the root, so the cockpit receives key events.
    focus: FocusHandle,
}

impl Cockpit {
    pub fn new(world: Rc<RefCell<World>>, anchors: [CellId; 3], focus: FocusHandle) -> Self {
        let cells = sorted_cells(&world.borrow());

        // Seed the debugger with a demo turn (treasury → user transfer) that
        // the operator can step + explain against the live world.
        let [treasury, service, user] = anchors;
        let debug_turn = world.borrow().turn(treasury, vec![world::transfer(treasury, user, 1_000)]);

        // Seed the cipherclerk vault with two real HD-derived identities.
        let mut clerk = cipherclerk::Cipherclerk::new();
        clerk.add_identity(cipherclerk::Identity::from_byte("alice", "dregg/cockpit", 0x01));
        clerk.add_identity(cipherclerk::Identity::from_byte("bob", "dregg/cockpit", 0x02));

        // Seed the editor with a conserving demo forest already validated.
        let mut editor = edit::EditorState::default();
        editor.set_artifact("Transfer 250 treasury→user (1 root, conserving)");
        {
            let mut fb = edit::ForestBuilder::new();
            fb.root(
                edit::ActionBuilder::new(treasury)
                    .effect(dregg_turn::action::Effect::Transfer { from: treasury, to: user, amount: 250 }),
            );
            editor.set_verdict(edit::validate(fb.forest()));
        }

        // Start the replay scrubber at the head of the live world's history.
        let replay_cursor = world.borrow().recorded_turns().len();

        // Boot the cap-first SHELL: open the privileged console surface (the
        // cockpit's own trusted root, run as the treasury/operator identity),
        // then open the three anchor cells as cap-confined cell-view surfaces so
        // the compositor boots into a LIVE multi-surface scene over real cells.
        let mut shell = Shell::new();
        let mut surface_caps = std::collections::HashMap::new();
        let console_cap = shell.open_console(treasury, "Master Console");
        let console_surface = console_cap.surface();
        surface_caps.insert(console_surface, console_cap);
        let mut service_surface = None;
        for (cell, name) in [(treasury, "Treasury"), (user, "User"), (service, "Service")] {
            let cap = shell.open_cell_view(cell, name);
            if cell == service {
                service_surface = Some(cap.surface());
            }
            surface_caps.insert(cap.surface(), cap);
        }
        // The AGENT-ACTIVITY surface: the service cell is the demo agent (it
        // holds a cap to the user cell — a real mandate — and commits cap-gated
        // turns in `demo_world`). Bind it as an agent surface so the Agent panel
        // renders its grounded-seam activity. Falls back to a fresh agent-view
        // surface id if the service surface somehow wasn't opened.
        let agent_surface = starbridge_v2::agent::AgentSurface::new(
            service_surface.unwrap_or(console_surface),
            service,
        );

        // The A1 EDITOR/BUFFER surface: a fresh dedicated cell backs the buffer
        // (its state slot carries the content digest; the cockpit holds the
        // WRITE cap the shell mints). Open it as a real shell surface so it
        // composites under the A0 verified scene like every other surface.
        let buffer_backing = world.borrow_mut().genesis_cell(0x5B, 0);
        let editor_buffer_cap = shell.open_cell_view(buffer_backing, "scratch.txt");
        surface_caps.insert(editor_buffer_cap.surface(), editor_buffer_cap.clone());
        let editor_buffer = BufferCell::new(
            editor_buffer_cap.surface(),
            buffer_backing,
            "scratch.txt",
            "// a cap-confined buffer — its digest rides a real cell.\n\
             // editing is free; COMMIT is a cap-gated verified turn.\n",
        );

        // The A1 TERMINAL surface: the SERVICE cell backs it — it holds a REAL
        // cap reaching the user cell (a genuine mandate), so a command targeting
        // the user is in-mandate (commits) and one targeting an out-of-reach cell
        // REFUSES (the ADOS tool-call seam, confined). Opened as a shell surface.
        let term_cap = shell.open_cell_view(service, "service-term");
        let terminal_surface = term_cap.surface();
        surface_caps.insert(terminal_surface, term_cap);
        let terminal = TerminalCell::new(terminal_surface, service, "service-term");

        // The A2 SWARM: service IS the coordinator (born holding a cap to user
        // in demo_world — its live mandate). User is worker-a (reachable from
        // service). Treasury is worker-b (NOT reachable from service, so the
        // swarm panel's cap-gate REFUSES any action targeting it — illustrating
        // the confined boundary). The swarm reads the real cap-graph.
        let swarm = {
            let w = world.borrow();
            Swarm::new(
                &w,
                [
                    (service, "coordinator"),
                    (user, "worker-a"),
                    (treasury, "worker-b (unreachable — the confinement boundary)"),
                ],
            )
        };

        Self {
            world,
            cells,
            selection: Selection::Image,
            last_outcome: None,
            anchors,
            tab: Tab::Shell,
            debug_turn,
            breakpoints: vec![debug::Breakpoint::OnRefusal, debug::Breakpoint::OnConservationBreak],
            replay_cursor,
            replay_fork: None,
            clerk,
            clerk_outcome: None,
            editor,
            shell,
            surface_caps,
            console_surface,
            frame_seq: 0,
            agent_surface,
            editor_buffer,
            editor_buffer_cap,
            terminal,
            swarm,
            palette: CommandPalette::new(),
            focus,
        }
    }

    fn refresh_cells(&mut self) {
        self.cells = sorted_cells(&self.world.borrow());
    }

    // --- the verbs (each runs the REAL embedded executor) -------------------

    fn run_demo_transfer(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::transfer(treasury, user, 1_000)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    fn run_demo_grant(&mut self, cx: &mut Context<Self>) {
        let [_treasury, service, user] = self.anchors;
        // Re-grant the service's user-cap to a fresh slot (legitimate).
        let outcome = {
            let mut w = self.world.borrow_mut();
            let slot = w
                .ledger()
                .get(&service)
                .map(|c| c.capabilities.len() as u32)
                .unwrap_or(0);
            let turn = w.turn(service, vec![world::grant_capability(service, service, user, slot)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    fn run_demo_create(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, _user] = self.anchors;
        let seed = (self.world.borrow().cell_count() as u8).wrapping_add(0x40);
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::create_cell(seed)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    fn run_over_grant(&mut self, cx: &mut Context<Self>) {
        // Demonstrate the ocap guarantee FIRING: an illegitimate grant.
        let [treasury, _service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            // treasury holds no cap to user → no-amplification rejects this.
            let turn = w.turn(treasury, vec![world::grant_capability(treasury, treasury, user, 0)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// Birth a fresh cell and SEAL it in one demo flow — shows the lifecycle
    /// verb running through the real executor (seal must target the acting cell;
    /// we genesis the cell, then seal it). Re-runnable: each press seals a new
    /// fresh cell so the lifecycle column grows.
    fn run_seal(&mut self, cx: &mut Context<Self>) {
        let outcome = {
            let mut w = self.world.borrow_mut();
            let seed = (w.cell_count() as u8).wrapping_add(0x70);
            let id = w.genesis_cell(seed, 0);
            let turn = w.turn(id, vec![world::seal(id, "operator seal demo")]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// Burn value from the treasury — supply provably reduced, no credit. The
    /// receipt's `was_burn` flag is bound into its hash (the cockpit's proof
    /// view surfaces it).
    fn run_burn(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, _user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::burn(treasury, 1_000)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// Compose a MULTI-ACTION turn — treasury pays BOTH service and user in one
    /// atomic verified turn (two sibling actions, one receipt). Demonstrates the
    /// call-forest composer driving the real executor.
    fn run_compose_multi(&mut self, cx: &mut Context<Self>) {
        let [treasury, service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.forest_turn(
                treasury,
                vec![
                    (treasury, vec![world::transfer(treasury, service, 500)]),
                    (treasury, vec![world::transfer(treasury, user, 750)]),
                ],
            );
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    // --- the CIPHERCLERK action loop (real macaroons) -----------------------
    //
    // These drive the REAL `AgentCipherclerk` via the `cipherclerk` action
    // layer (mint → attenuate → delegate → discharge). The demo acts on the two
    // seeded identities (alice mints/attenuates/delegates; bob receives) and the
    // "dns" service, so the operator can watch the wallet + delegation vault
    // grow and see the discharge verdict.

    fn run_clerk_mint(&mut self, cx: &mut Context<Self>) {
        let out = self.clerk.mint("alice", "dns");
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    fn run_clerk_attenuate(&mut self, cx: &mut Context<Self>) {
        // Confine alice's dns root to read-only with a far-future expiry.
        let out = self.clerk.attenuate_latest("alice", "dns", "r", Some(4_000_000_000));
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    fn run_clerk_delegate(&mut self, cx: &mut Context<Self>) {
        // Hand a dns/read capability to bob as a real signed envelope.
        let out = self.clerk.delegate_to("alice", "bob", "dns", "r");
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    fn run_clerk_discharge(&mut self, cx: &mut Context<Self>) {
        // Discharge alice's dns token against an atomic 'r' (read) request now.
        // (The macaroon action vocabulary is the atomic letters r/w/c/d/C.)
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        let out = self.clerk.discharge("alice", "dns", "r", now);
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    // --- the A1 EDITOR/BUFFER surface ops (cap-gated edits) ------------------
    //
    // Editing the buffer's text is free (an in-memory doc edit); LANDING it is a
    // cap-gated verified turn — the cockpit presents the WRITE cap and the
    // backing cell's digest advances (a real receipt). A read-only buffer would
    // refuse — the no-amplification rule at the editor.

    /// Type a line into the editor buffer (free, in-memory) — the operator can
    /// watch the doc become DIRTY (its digest now differs from the committed one).
    fn buffer_type_demo(&mut self, cx: &mut Context<Self>) {
        let stamp = self.world.borrow().height();
        self.editor_buffer
            .doc_mut()
            .insert(&format!("edit @ h{stamp}\n"));
        self.last_outcome = Some(
            "buffer: typed a line (in-memory — the doc is now DIRTY until a cap-gated commit)"
                .to_string(),
        );
        self.tab = Tab::Buffer;
        cx.notify();
    }

    /// COMMIT the editor buffer — write its digest into the backing cell through
    /// a REAL verified turn (cap-gated; the cockpit presents the WRITE cap).
    fn buffer_commit(&mut self, cx: &mut Context<Self>) {
        let cap = self.editor_buffer_cap.clone();
        let result = {
            let mut w = self.world.borrow_mut();
            self.editor_buffer.commit(&mut w, &cap)
        };
        self.last_outcome = Some(match result {
            Ok(rev) => format!(
                "buffer: COMMITTED — digest written to the backing cell as a verified turn (revision {rev})"
            ),
            Err(e) => format!("buffer: commit REFUSED — {}", e.explain()),
        });
        self.refresh_cells();
        self.tab = Tab::Buffer;
        cx.notify();
    }

    /// Attempt to COMMIT through a READ-ONLY mirror — the no-amplification rule
    /// firing at the editor. The cockpit narrows its write cap to a read-only
    /// (Signature) mirror via a REAL GrantCapability share, then tries to commit
    /// through it: the buffer-cap gate REFUSES (a read-only buffer cannot write).
    fn buffer_readonly_write_demo(&mut self, cx: &mut Context<Self>) {
        let cap = self.editor_buffer_cap.clone();
        // Narrow to a read-only mirror through the real executor (None → Signature).
        let mirror = match self.shell.share(&cap, /*peer app*/ 0x4E0, dregg_cell::AuthRequired::Signature) {
            Ok(m) => m,
            Err(e) => {
                self.last_outcome = Some(format!("buffer: could not make a read-only mirror — {}", shell_err(&e)));
                cx.notify();
                return;
            }
        };
        self.surface_caps.insert(mirror.surface(), mirror.clone());
        // A read-only buffer rendered into the mirror's surface.
        let ro_buffer = BufferCell::new(
            mirror.surface(),
            self.editor_buffer.backing(),
            "scratch.txt (read-only mirror)",
            self.editor_buffer.doc().text(),
        );
        let result = {
            let mut w = self.world.borrow_mut();
            ro_buffer.commit(&mut w, &mirror)
        };
        self.last_outcome = Some(match result {
            Ok(_) => "buffer: read-only write UNEXPECTEDLY committed (should have refused!)".to_string(),
            Err(e) => format!("buffer: ⚠ read-only write REFUSED — {} (no-amplification at the editor)", e.explain()),
        });
        self.tab = Tab::Buffer;
        cx.notify();
    }

    // --- the A1 TERMINAL surface ops (the ADOS tool-call seam) ---------------
    //
    // A command is cap-gated on the terminal-cell's c-list: an in-mandate target
    // COMMITS (its receipt is the output); an out-of-mandate one REFUSES. This is
    // the agent's Bash confined to its mandate, made a surface.

    /// Run an IN-MANDATE command — the service terminal-cell holds a cap reaching
    /// the user cell, so a transfer to the user COMMITS (its receipt is the output).
    fn terminal_run_in_mandate(&mut self, cx: &mut Context<Self>) {
        let [_treasury, _service, user] = self.anchors;
        let line = {
            let mut w = self.world.borrow_mut();
            self.terminal.run(&mut w, Command::Transfer { target: user, amount: 100 })
        };
        self.last_outcome = Some(match line {
            Ok(l) => format!("terminal: command COMMITTED — {} (receipt is the output)", l.result),
            Err(e) => format!("terminal: command REFUSED — {}", e.explain()),
        });
        self.refresh_cells();
        self.tab = Tab::Terminal;
        cx.notify();
    }

    /// Run an OUT-OF-MANDATE command — target a cell the terminal-cell holds NO
    /// cap for; the command cap-gate REFUSES it (the agent's Bash confined). Uses
    /// the treasury (the service holds no cap reaching it).
    fn terminal_run_out_of_mandate(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, _user] = self.anchors;
        let line = {
            let mut w = self.world.borrow_mut();
            self.terminal.run(&mut w, Command::Transfer { target: treasury, amount: 1 })
        };
        self.last_outcome = Some(match line {
            Ok(_) => "terminal: out-of-mandate command UNEXPECTEDLY committed (should have refused!)".to_string(),
            Err(e) => format!("terminal: ⚠ command REFUSED — {} (cap-gate, BEFORE any turn)", e.explain()),
        });
        self.tab = Tab::Terminal;
        cx.notify();
    }

    // --- the A2 SWARM surface ops (notify-edge-routed cap-coordination) ------

    /// Swarm action: coordinator EMITS a notify event targeting worker-a.
    /// This is the grounded seam: the emit is a cap-gated turn; the
    /// `NotifyEdge` lands in worker-a's inbox (async, NOT a joint turn).
    /// Swarm layout: service = coordinator (cap to user), user = worker-a.
    fn swarm_coordinator_emit_a(&mut self, cx: &mut Context<Self>) {
        let [_treasury, coord, worker_a] = self.anchors; // service=coord, user=worker-a
        let outcome = {
            let mut w = self.world.borrow_mut();
            self.swarm.run(&mut w, coord, vec![world::emit_event(worker_a, "task/go", vec![])])
        };
        self.last_outcome = Some(match &outcome {
            Ok(ao) => format!(
                "swarm: coordinator emitted task/go → worker-a (receipt {}) — {} notify edge(s) deposited",
                ao.receipt_hash.map(|h| reflect::short_hex(&h)).unwrap_or_default(),
                ao.notify_edges.len(),
            ),
            Err(e) => format!("swarm: REFUSED — {}", e.label()),
        });
        self.refresh_cells();
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// Swarm action: worker-a DRAINS its pending notification (its own async ack turn).
    /// This is a wholly independent turn from the coordinator's emit — different
    /// receipt, different height, different provenance. The async model at work.
    fn swarm_worker_a_drain(&mut self, cx: &mut Context<Self>) {
        let [_treasury, _coord, worker_a] = self.anchors; // user=worker-a
        let outcome = {
            let mut w = self.world.borrow_mut();
            self.swarm.drain_notify(&mut w, worker_a)
        };
        self.last_outcome = Some(match outcome {
            Ok(receipt) => format!(
                "swarm: worker-a DRAINED its notify inbox (ack receipt {}) — async, separate from sender's turn",
                reflect::short_hex(&receipt),
            ),
            Err(e) => format!("swarm: drain REFUSED — {}", e.label()),
        });
        self.refresh_cells();
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// Swarm action: coordinator (service) sends value to worker-a (user) AND emits
    /// a wake to worker-a, in ONE multi-effect turn. One seam, two effects, real receipt.
    /// (worker-b = treasury = unreachable from service; transfer to treasury would REFUSE.)
    fn swarm_coordinator_transfer_and_wake(&mut self, cx: &mut Context<Self>) {
        let [_treasury, coord, worker_a] = self.anchors; // service=coord, user=worker-a
        let outcome = {
            let mut w = self.world.borrow_mut();
            self.swarm.run(
                &mut w,
                coord,
                vec![
                    world::transfer(coord, worker_a, 500),
                    world::emit_event(worker_a, "task/done", vec![]),
                ],
            )
        };
        self.last_outcome = Some(match &outcome {
            Ok(ao) => format!(
                "swarm: coordinator transferred 500 + woke worker-a (receipt {}) — {} notify edge(s)",
                ao.receipt_hash.map(|h| reflect::short_hex(&h)).unwrap_or_default(),
                ao.notify_edges.len(),
            ),
            Err(e) => format!("swarm: REFUSED — {}", e.label()),
        });
        self.refresh_cells();
        self.tab = Tab::Swarm;
        cx.notify();
    }

    // --- replay scrubber + debugger retarget (palette-drivable) -------------

    fn replay_step_back(&mut self, cx: &mut Context<Self>) {
        self.replay_cursor = self.replay_cursor.saturating_sub(1);
        cx.notify();
    }

    fn replay_step_forward(&mut self, cx: &mut Context<Self>) {
        let len = self.world.borrow().recorded_turns().len();
        self.replay_cursor = (self.replay_cursor + 1).min(len);
        cx.notify();
    }

    fn replay_to_genesis(&mut self, cx: &mut Context<Self>) {
        self.replay_cursor = 0;
        cx.notify();
    }

    fn replay_to_head(&mut self, cx: &mut Context<Self>) {
        self.replay_cursor = self.world.borrow().recorded_turns().len();
        cx.notify();
    }

    /// Pin a what-if FORK at the current scrubber cursor: re-run the cursor's
    /// real turn as the "alternate" (a no-op divergence baseline) so the panel
    /// shows the fork machinery live. (A richer alt-turn editor is a follow-on;
    /// this proves the verified-fork path through the palette.)
    fn replay_fork_here(&mut self, cx: &mut Context<Self>) {
        let w = self.world.borrow();
        let history = w.recorded_turns();
        let k = self.replay_cursor.min(history.len());
        // Use the treasury anchor for a representative alternate transfer.
        let [treasury, _service, user] = self.anchors;
        // A small alternate transfer the branch point can apply.
        let alt = world::bare_turn(
            treasury,
            history
                .replay_to(k)
                .ok()
                .and_then(|l| l.get(&treasury).map(|c| c.state.nonce()))
                .unwrap_or(0),
            vec![world::transfer(treasury, user, 1)],
        );
        match history.fork_at(k, alt) {
            Ok(fork) => {
                drop(w);
                self.replay_fork = Some(fork);
            }
            Err(_) => {
                drop(w);
                self.replay_fork = None;
            }
        }
        cx.notify();
    }

    fn replay_clear_fork(&mut self, cx: &mut Context<Self>) {
        self.replay_fork = None;
        cx.notify();
    }

    /// Retarget the debugger to a transfer FROM the currently-selected cell (so
    /// the operator can step any cell's outgoing turn, not just the seeded one).
    fn debug_retarget_selected(&mut self, cx: &mut Context<Self>) {
        if let Selection::Cell(id) = self.selection {
            let [_t, _s, user] = self.anchors;
            // Target = the selected cell; pay a token amount to `user` so there
            // is an effect to step (the debugger re-executes faithfully).
            let to = if user == id { self.anchors[0] } else { user };
            self.debug_turn = self.world.borrow().turn(id, vec![world::transfer(id, to, 100)]);
            self.tab = Tab::Debugger;
            cx.notify();
        } else {
            self.last_outcome = Some("debugger retarget: select a cell first".to_string());
            cx.notify();
        }
    }

    // --- the cap-first SHELL ops (each routes through the CAP-GATED shell) ---
    //
    // The cockpit IS the operator: it holds every surface's cap in `surface_caps`.
    // But it can ONLY drive a surface by presenting that cap to the shell's
    // gated API — so the window manager's ocap discipline is demonstrated, not
    // bypassed. (A window op with no held cap simply has nothing to present and
    // is refused — exactly the no-ambient-authority property.)

    /// Open the currently-selected cell as a new cap-confined SURFACE. The shell
    /// mints the surface's cap; the cockpit files it in its vault. (Opening a
    /// cell that isn't selected falls back to the service anchor so the verb is
    /// always live.)
    fn shell_open_selected(&mut self, cx: &mut Context<Self>) {
        let cell = match self.selection {
            Selection::Cell(id) => id,
            _ => self.anchors[1], // service, as a sensible default
        };
        let short = reflect::short_hex(cell.as_bytes());
        let cap = self.shell.open_cell_view(cell, format!("cell {short}"));
        self.surface_caps.insert(cap.surface(), cap);
        self.last_outcome = Some(format!("shell: opened surface for cell {short} (cap minted)"));
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Focus + raise the front-most NON-console surface (a cap-gated op). The
    /// cockpit presents the held cap; the shell authenticates it before raising.
    fn shell_focus_front(&mut self, cx: &mut Context<Self>) {
        // Find the current front non-console surface in the live scene.
        let front = {
            let w = self.world.borrow();
            let scene = self.shell.compose(&w);
            scene
                .items
                .iter()
                .rev()
                .find(|it| !it.surface.is_console())
                .map(|it| it.surface.id())
        };
        if let Some(id) = front {
            self.with_cap(id, |shell, cap| shell.focus(cap), cx, "focus");
        } else {
            self.last_outcome = Some("shell: no cell surface to focus".to_string());
            cx.notify();
        }
    }

    /// Close the focused surface (cap-gated; the console is protected, so closing
    /// it is refused — a refusal the operator can watch). The cap is dropped when
    /// the surface closes.
    fn shell_close_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to close".to_string());
            cx.notify();
            return;
        };
        let outcome = match self.surface_caps.get(&id) {
            Some(cap) => self.shell.close(cap),
            None => Err(starbridge_v2::shell::ShellError::Unauthorized),
        };
        match outcome {
            Ok(()) => {
                self.surface_caps.remove(&id);
                self.last_outcome = Some("shell: closed the focused surface (cap retired)".to_string());
            }
            Err(e) => {
                self.last_outcome = Some(format!("shell: close REFUSED — {}", shell_err(&e)));
            }
        }
        cx.notify();
    }

    /// Minimize the focused surface (cap-gated).
    fn shell_minimize_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to minimize".to_string());
            cx.notify();
            return;
        };
        self.with_cap(id, |shell, cap| shell.set_minimized(cap, true), cx, "minimize");
    }

    /// SHARE the focused window with another app — an ATTENUATING (read-only
    /// mirror) hand-off through a REAL `Effect::GrantCapability` turn on the
    /// firmament executor. Commits; the recipient's narrowed window cap is filed
    /// in the vault (so its shared window is drivable), demonstrating "a window =
    /// a firmament cap" delegated through the real executor — granted ⊆ held.
    fn shell_share_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to share".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        // Hand a READ-ONLY mirror (Signature ⊆ the held rights) to a peer app.
        match self.shell.share(&cap, /*peer app*/ 0x5EED, dregg_cell::AuthRequired::Signature) {
            Ok(shared) => {
                self.surface_caps.insert(shared.surface(), shared);
                self.last_outcome = Some(
                    "shell: shared a read-only window mirror (real GrantCapability turn committed)"
                        .to_string(),
                );
            }
            Err(e) => {
                self.last_outcome = Some(format!("shell: share REFUSED — {}", shell_err(&e)));
            }
        }
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// ⚠ Attempt to OVER-SHARE the focused window — the no-amplification
    /// guarantee firing at the desktop. We first share a read-only mirror to a
    /// peer (commits), then have THAT peer try to re-share its window with WIDER
    /// authority than it holds; the REAL executor REJECTS the widening
    /// (`DelegationDenied`). This is the window-manager analogue of the composer's
    /// ⚠ over-grant verb — a refusal the operator can watch.
    fn shell_overshare_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to over-share".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        // Step 1: legitimately hand a peer a read-only mirror (commits).
        let mirror = match self.shell.share(&cap, /*peer*/ 0xA11CE, dregg_cell::AuthRequired::Signature) {
            Ok(m) => m,
            Err(e) => {
                self.last_outcome = Some(format!("shell: setup share failed — {}", shell_err(&e)));
                cx.notify();
                return;
            }
        };
        self.surface_caps.insert(mirror.surface(), mirror.clone());
        // Step 2: that read-only-mirror peer tries to OVER-SHARE (Signature →
        // Either is WIDER). The real executor REJECTS it — watch it fire.
        match self.shell.share(&mirror, /*victim*/ 0xBAD, dregg_cell::AuthRequired::Either) {
            Ok(_) => {
                self.last_outcome =
                    Some("shell: over-share UNEXPECTEDLY committed (should have rejected!)".to_string());
            }
            Err(e) => {
                self.last_outcome = Some(format!(
                    "shell: ⚠ over-share REJECTED by the real executor — {} (no-amplification on glass)",
                    shell_err(&e)
                ));
            }
        }
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Cycle the compositor layout (float → tile → stack). A shell-global op (it
    /// rearranges the whole scene), so it is not surface-cap-scoped.
    fn shell_cycle_layout(&mut self, cx: &mut Context<Self>) {
        self.shell.cycle_layout();
        self.last_outcome = Some(format!("shell: layout → {}", self.shell.layout().label()));
        self.tab = Tab::Shell;
        cx.notify();
    }

    // --- THE VERIFIED-SCENE teaching moments (T1/T2/T3 at the pixel layer) ---
    //
    // These exercise the compositor's `present()` path so the operator can WATCH
    // the scene-authority teeth bite — exactly the over-share teaching moment,
    // one hop out (the no-amplification guarantee firing at the GLASS).

    /// PRESENT honestly from the FOCUSED surface: paint its own region, claim
    /// focus (it IS the focus holder), advance the frame. COMMITS — the scene
    /// the operator sees is the genuine projection (the commit polarity).
    fn shell_present_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to present".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        let region = id.region();
        let digest = self.next_frame_digest();
        let w = self.world.borrow();
        match self.shell.present(&cap, &w, vec![region], /*claims_focus*/ true, digest) {
            Ok(commit) => {
                self.last_outcome = Some(format!(
                    "shell: present COMMITTED — frame {} on the focused surface (genuine projection)",
                    commit.digest
                ));
            }
            Err(e) => {
                self.last_outcome = Some(format!("shell: present REFUSED — {}", shell_err(&e)));
            }
        }
        drop(w);
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Attempt an OVERPAINT: the focused surface tries to paint the FRONT OTHER
    /// surface's region — the T1 non-overlap tooth REFUSES it (a cell cannot
    /// paint a region another cell owns). The pixel-layer over-grant.
    fn shell_overpaint_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to present".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        // Compute the frame digest BEFORE borrowing the world (the digest
        // counter is `&mut self`; the present below holds an immutable borrow).
        let digest = self.next_frame_digest();
        // Find ANOTHER surface's region to overpaint (a genuinely-distinct attack
        // — a real second surface's region, not a malformed one).
        let w = self.world.borrow();
        let victim_region = self
            .shell
            .compose_scene(&w)
            .surfaces
            .iter()
            .find(|s| Some(s.owner) != self.shell.focused_cell())
            .and_then(|s| s.regions.first().copied());
        let Some(victim_region) = victim_region else {
            drop(w);
            self.last_outcome =
                Some("shell: need a second surface to demo an overpaint".to_string());
            cx.notify();
            return;
        };
        match self.shell.present(&cap, &w, vec![victim_region], true, digest) {
            Ok(_) => {
                self.last_outcome = Some(
                    "shell: overpaint UNEXPECTEDLY committed (should have rejected!)".to_string(),
                );
            }
            Err(e) => {
                self.last_outcome = Some(format!(
                    "shell: ⚠ overpaint REFUSED by the verified scene — {} (T1 no-amplification on glass)",
                    shell_err(&e)
                ));
            }
        }
        drop(w);
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Attempt an INPUT-STEAL: a NON-focused surface presents its own region but
    /// asserts input focus to steal the keystroke — the T3 input-routing tooth
    /// REFUSES it (input routes only to the focus holder).
    fn shell_input_steal(&mut self, cx: &mut Context<Self>) {
        // Compute the frame digest BEFORE borrowing the world (the digest counter
        // is `&mut self`; the present below holds an immutable borrow of it).
        let digest = self.next_frame_digest();
        // Find a non-focused, non-console surface to play the thief.
        let w = self.world.borrow();
        let thief = self
            .shell
            .surfaces_in_z_order()
            .into_iter()
            .find(|s| !s.is_console() && Some(s.id()) != self.shell.focused())
            .map(|s| s.id());
        let Some(thief) = thief else {
            drop(w);
            self.last_outcome =
                Some("shell: need a second surface to demo an input-steal".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&thief).cloned() else {
            drop(w);
            self.last_outcome = Some("shell: no held cap for the thief surface".to_string());
            cx.notify();
            return;
        };
        let region = thief.region();
        match self.shell.present(&cap, &w, vec![region], /*claims_focus*/ true, digest) {
            Ok(_) => {
                self.last_outcome = Some(
                    "shell: input-steal UNEXPECTEDLY committed (should have rejected!)".to_string(),
                );
            }
            Err(e) => {
                self.last_outcome = Some(format!(
                    "shell: ⚠ input-steal REFUSED by the verified scene — {} (T3 only the focus holder gets input)",
                    shell_err(&e)
                ));
            }
        }
        drop(w);
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// A monotonic frame digest for the present teaching moments (so every
    /// present genuinely advances the frame — the Lean `new ≠ old` leg).
    fn next_frame_digest(&mut self) -> u64 {
        self.frame_seq = self.frame_seq.wrapping_add(1);
        0xF00D_0000 + self.frame_seq
    }

    /// Focus a surface by id when the operator clicks it in the scene. The click
    /// is only a HINT — the cockpit then presents the held cap, and the shell's
    /// cap-gated `focus` is the actual authority (no held cap ⇒ no focus).
    fn shell_click_surface(&mut self, id: SurfaceId, cx: &mut Context<Self>) {
        self.with_cap(id, |shell, cap| shell.focus(cap), cx, "focus");
    }

    /// Drive a cap-gated shell op for surface `id`: look up the held cap, present
    /// it to the shell, and surface the verdict. Centralizes the "present the
    /// cap or it's refused" discipline so every op goes through it.
    fn with_cap<F>(&mut self, id: SurfaceId, op: F, cx: &mut Context<Self>, what: &str)
    where
        F: FnOnce(&mut Shell, &SurfaceCapability) -> Result<(), starbridge_v2::shell::ShellError>,
    {
        let result = match self.surface_caps.get(&id) {
            Some(cap) => op(&mut self.shell, cap),
            // No held cap for this surface → nothing to present → refused. This
            // IS the no-ambient-authority property (you can't act without a cap).
            None => Err(starbridge_v2::shell::ShellError::Unauthorized),
        };
        if let Err(e) = result {
            self.last_outcome = Some(format!("shell: {what} REFUSED — {}", shell_err(&e)));
        }
        cx.notify();
    }

    // --- THE CENTRAL DISPATCHER — one path for buttons AND the palette -------

    /// Run a palette [`CommandId`] through the SAME `&mut Cockpit` verbs the
    /// buttons call. This is what keeps the ⌘K palette honestly "over ALL
    /// actions": there is no parallel action path — every command lands here and
    /// routes to the one method that already implements it.
    fn dispatch(&mut self, id: CommandId, cx: &mut Context<Self>) {
        match id {
            CommandId::Transfer => self.run_demo_transfer(cx),
            CommandId::ComposeMulti => self.run_compose_multi(cx),
            CommandId::Grant => self.run_demo_grant(cx),
            CommandId::CreateCell => self.run_demo_create(cx),
            CommandId::Seal => self.run_seal(cx),
            CommandId::Burn => self.run_burn(cx),
            CommandId::OverGrant => self.run_over_grant(cx),

            CommandId::GoComposer => self.set_tab(Tab::Composer, cx),
            CommandId::GoObjects => self.set_tab(Tab::Objects, cx),
            CommandId::GoDebugger => self.set_tab(Tab::Debugger, cx),
            CommandId::GoReplay => self.set_tab(Tab::Replay, cx),
            CommandId::GoCipherclerk => self.set_tab(Tab::Cipherclerk, cx),
            CommandId::GoEditor => self.set_tab(Tab::Editor, cx),
            CommandId::GoShell => self.set_tab(Tab::Shell, cx),
            CommandId::GoAgent => self.set_tab(Tab::Agent, cx),
            CommandId::GoBuffer => self.set_tab(Tab::Buffer, cx),
            CommandId::GoTerminal => self.set_tab(Tab::Terminal, cx),
            CommandId::GoSwarm => self.set_tab(Tab::Swarm, cx),
            CommandId::GoGraph => self.set_tab(Tab::Graph, cx),
            CommandId::GoOrgans => self.set_tab(Tab::Organs, cx),
            CommandId::GoProofs => self.set_tab(Tab::Proofs, cx),

            CommandId::BufferType => self.buffer_type_demo(cx),
            CommandId::BufferCommit => self.buffer_commit(cx),
            CommandId::BufferReadOnlyWrite => self.buffer_readonly_write_demo(cx),
            CommandId::TerminalRunInMandate => self.terminal_run_in_mandate(cx),
            CommandId::TerminalRunOutOfMandate => self.terminal_run_out_of_mandate(cx),

            CommandId::SwarmCoordinatorEmitA => self.swarm_coordinator_emit_a(cx),
            CommandId::SwarmWorkerADrain => self.swarm_worker_a_drain(cx),
            CommandId::SwarmCoordinatorTransferAndWake => {
                self.swarm_coordinator_transfer_and_wake(cx)
            }

            CommandId::ShellOpenSelected => self.shell_open_selected(cx),
            CommandId::ShellFocusFront => self.shell_focus_front(cx),
            CommandId::ShellCloseFocused => self.shell_close_focused(cx),
            CommandId::ShellCycleLayout => self.shell_cycle_layout(cx),
            CommandId::ShellMinimizeFocused => self.shell_minimize_focused(cx),
            CommandId::ShellShareFocused => self.shell_share_focused(cx),
            CommandId::ShellOverShareFocused => self.shell_overshare_focused(cx),
            CommandId::ShellPresentFocused => self.shell_present_focused(cx),
            CommandId::ShellOverpaintFocused => self.shell_overpaint_focused(cx),
            CommandId::ShellInputSteal => self.shell_input_steal(cx),

            CommandId::ReplayStepBack => self.replay_step_back(cx),
            CommandId::ReplayStepForward => self.replay_step_forward(cx),
            CommandId::ReplayToGenesis => self.replay_to_genesis(cx),
            CommandId::ReplayToHead => self.replay_to_head(cx),
            CommandId::ReplayForkHere => self.replay_fork_here(cx),
            CommandId::ReplayClearFork => self.replay_clear_fork(cx),

            CommandId::ClerkMint => self.run_clerk_mint(cx),
            CommandId::ClerkAttenuate => self.run_clerk_attenuate(cx),
            CommandId::ClerkDelegate => self.run_clerk_delegate(cx),
            CommandId::ClerkDischarge => self.run_clerk_discharge(cx),

            CommandId::DebugRetargetSelected => self.debug_retarget_selected(cx),
            CommandId::SelectImage => {
                self.selection = Selection::Image;
                cx.notify();
            }
            CommandId::Dismiss => {
                self.palette.close();
                cx.notify();
            }
        }
    }

    fn set_tab(&mut self, tab: Tab, cx: &mut Context<Self>) {
        self.tab = tab;
        cx.notify();
    }

    /// Focus the cockpit root so it receives key events (called on window open).
    pub fn focus_on_open(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        window.focus(&self.focus, cx);
    }

    // --- the ⌘K key handler -------------------------------------------------

    /// Handle a key event. ⌘K toggles the palette; while it is open, typed
    /// characters filter, ↑/↓ move the selection, Enter dispatches, Esc closes.
    /// Returns nothing — it mutates palette state + may dispatch a command.
    fn on_key(&mut self, ev: &KeyDownEvent, cx: &mut Context<Self>) {
        let ks = &ev.keystroke;
        let key = ks.key.as_str();
        let cmd = ks.modifiers.platform || ks.modifiers.control;

        // ⌘K / Ctrl-K toggles the palette from anywhere.
        if cmd && key == "k" {
            self.palette.toggle();
            cx.notify();
            return;
        }

        if !self.palette.is_open() {
            return;
        }

        match key {
            "escape" => {
                self.palette.close();
                cx.notify();
            }
            "enter" => {
                if let Some(id) = self.palette.accept() {
                    self.dispatch(id, cx);
                }
                cx.notify();
            }
            "backspace" => {
                self.palette.backspace();
                cx.notify();
            }
            "down" => {
                self.palette.select_next();
                cx.notify();
            }
            "up" => {
                self.palette.select_prev();
                cx.notify();
            }
            _ => {
                // A typed character (cmd not held) filters the query.
                if !cmd {
                    if let Some(ch) = ks.key_char.as_ref().and_then(|s| s.chars().next()) {
                        if !ch.is_control() {
                            self.palette.push_char(ch);
                            cx.notify();
                        }
                    }
                }
            }
        }
    }

    fn note_outcome(&mut self, outcome: CommitOutcome) {
        self.last_outcome = Some(match outcome {
            CommitOutcome::Committed { receipt, .. } => {
                // Jump the inspector to the new receipt.
                let idx = self.world.borrow().receipts().len().saturating_sub(1);
                self.selection = Selection::Receipt(idx);
                format!("committed · receipt {}", reflect::short_hex(&receipt.receipt_hash()))
            }
            CommitOutcome::Rejected { reason, .. } => format!("REJECTED by executor: {reason}"),
        });
    }

    // --- panels --------------------------------------------------------------

    fn rail_header(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let root = reflect::short_hex(&w.state_root());
        div()
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .border_b_1()
            .border_color(theme::border())
            .child(div().text_lg().text_color(theme::text()).child("Starbridge v2"))
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("the live, verified, ocap image"),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::accent())
                    .child("⌘K · command palette (every action)"),
            )
            .child(
                div()
                    .flex()
                    .gap_2()
                    .mt_2()
                    .child(pill("embedded executor", theme::good()))
                    .child(pill(format!("h{}", w.height()), theme::accent())),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!("image root: {root}")),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!(
                        "{} cells · {} receipts",
                        w.cell_count(),
                        w.receipts().len()
                    )),
            )
    }

    fn cell_world(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().p_2();
        col = col.child(section_title("CELL WORLD · ocap").mb_1());
        // The image object itself, selectable.
        col = col.child(self.image_row(cx));
        for id in &self.cells {
            if let Some(cell) = w.ledger().get(id) {
                col = col.child(self.cell_row(*id, cell, cx));
            }
        }
        col
    }

    fn image_row(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = matches!(self.selection, Selection::Image);
        div()
            .id("image-row")
            .flex()
            .justify_between()
            .px_2()
            .py_1()
            .rounded_md()
            .bg(if selected { theme::panel_hi() } else { theme::panel() })
            .cursor_pointer()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|this, _ev, _w, cx| {
                    this.selection = Selection::Image;
                    cx.notify();
                }),
            )
            .child(div().text_color(theme::accent()).child("◆ this image"))
    }

    fn cell_row(&self, id: CellId, cell: &dregg_cell::Cell, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = matches!(self.selection, Selection::Cell(s) if s == id);
        let bal = cell.state.balance();
        let caps = cell.capabilities.len();
        let bal_color = if bal < 0 { theme::warn() } else { theme::text() };
        div()
            .id(SharedString::from(format!("cell-{}", reflect::short_hex(id.as_bytes()))))
            .flex()
            .flex_col()
            .gap_0p5()
            .px_2()
            .py_1()
            .rounded_md()
            .bg(if selected { theme::panel_hi() } else { theme::panel() })
            .cursor_pointer()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev, _w, cx| {
                    this.selection = Selection::Cell(id);
                    cx.notify();
                }),
            )
            .child(
                div()
                    .flex()
                    .justify_between()
                    .child(div().text_color(theme::text()).child(format!("⬡ {}", reflect::short_hex(id.as_bytes()))))
                    .child(div().text_color(bal_color).child(format!("{bal}"))),
            )
            .child(
                div()
                    .flex()
                    .gap_2()
                    .child(div().text_xs().text_color(theme::muted()).child(format!("{caps} caps")))
                    .when(cell.delegate.is_some(), |d| {
                        d.child(div().text_xs().text_color(theme::muted()).child("delegate"))
                    })
                    .when(!matches!(cell.program, dregg_cell::CellProgram::None), |d| {
                        d.child(div().text_xs().text_color(theme::accent()).child("program"))
                    }),
            )
    }

    fn inspector(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let obj: Option<Inspectable> = match &self.selection {
            Selection::Image => Some(reflect::reflect_image(&w)),
            Selection::Cell(id) => w.ledger().get(id).map(|c| reflect::reflect_cell(id, c)),
            Selection::Receipt(i) => w.receipts().get(*i).map(reflect::reflect_receipt),
        };
        let mut panel = div().flex().flex_col().gap_1().p_3().size_full();
        panel = panel.child(section_title("INSPECTOR · reflective").mb_1());
        match obj {
            Some(obj) => {
                panel = panel.child(
                    div().text_color(theme::text()).child(obj.title.clone()),
                );
                panel = panel.child(
                    div().text_xs().text_color(theme::muted()).mb_2().child(obj.subtitle.clone()),
                );
                panel = panel.child(kind_badge(obj.kind));
                for f in &obj.fields {
                    panel = panel.child(field_row(f));
                }
            }
            None => {
                panel = panel.child(div().text_color(theme::muted()).child("(nothing selected)"));
            }
        }
        panel
    }

    fn blocklace(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().p_2();
        col = col.child(section_title("BLOCKLACE · provenance").mb_1());
        if w.receipts().is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child("(no receipts yet — run a verb)"));
        }
        // Most-recent first.
        for (i, r) in w.receipts().iter().enumerate().rev() {
            let selected = matches!(self.selection, Selection::Receipt(s) if s == i);
            let hash = reflect::short_hex(&r.receipt_hash());
            col = col.child(
                div()
                    .id(SharedString::from(format!("rcpt-{i}")))
                    .flex()
                    .justify_between()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if selected { theme::panel_hi() } else { theme::panel() })
                    .cursor_pointer()
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.selection = Selection::Receipt(i);
                            cx.notify();
                        }),
                    )
                    .child(div().text_xs().text_color(theme::accent()).child(format!("●─ {hash}")))
                    .child(div().text_xs().text_color(theme::muted()).child(format!("{} eff", r.action_count))),
            );
        }
        col
    }

    fn composer(&self, cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .child(section_title("COMPOSER · drive the executor"))
            .child(div().text_xs().text_color(theme::muted()).child(
                "Each verb composes a turn and runs it through the EMBEDDED VERIFIED executor. \
                 Watch the image, receipts, and dynamics update live.",
            ))
            .child(verb_button(cx, "transfer 1,000 → user", theme::good(), Cockpit::run_demo_transfer))
            .child(verb_button(cx, "compose multi-action (pay service + user)", theme::good(), Cockpit::run_compose_multi))
            .child(verb_button(cx, "grant capability (service→user)", theme::accent(), Cockpit::run_demo_grant))
            .child(verb_button(cx, "create cell (conserves value)", theme::accent(), Cockpit::run_demo_create))
            .child(verb_button(cx, "seal a fresh cell (lifecycle)", theme::accent(), Cockpit::run_seal))
            .child(verb_button(cx, "burn 1,000 (supply reduced)", theme::warn(), Cockpit::run_burn))
            .child(verb_button(cx, "⚠ over-grant (watch it REJECT)", theme::warn(), Cockpit::run_over_grant))
            .child(self.outcome_banner())
    }

    fn outcome_banner(&self) -> impl IntoElement {
        let (txt, color) = match &self.last_outcome {
            // A rejected turn OR a refused shell op — the guarantee firing.
            Some(s) if s.contains("REJECTED") || s.contains("REFUSED") => (s.clone(), theme::bad()),
            Some(s) => (s.clone(), theme::good()),
            None => ("(no turn run yet)".to_string(), theme::muted()),
        };
        div()
            .mt_2()
            .p_2()
            .rounded_md()
            .bg(theme::panel())
            .text_xs()
            .text_color(color)
            .child(txt)
    }

    fn dynamics_feed(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_0p5().p_2();
        col = col.child(section_title("DYNAMICS · live").mb_1());
        let tail = w.dynamics().tail(12);
        if tail.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child("(quiet)"));
        }
        for ev in tail.iter().rev() {
            let is_reject = matches!(ev, dynamics::WorldEvent::TurnRejected { .. });
            col = col.child(
                div()
                    .text_xs()
                    .text_color(if is_reject { theme::bad() } else { theme::muted() })
                    .child(format!("· {}", ev.label())),
            );
        }
        col
    }

    // --- the workspace tab bar + the four feature panels ---------------------

    /// The tab strip that switches the right-pane workspace.
    fn tab_bar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let mut row = div().flex().gap_1().p_2().border_b_1().border_color(theme::border());
        for t in Tab::ALL {
            let active = self.tab == t;
            row = row.child(
                div()
                    .id(SharedString::from(format!("tab-{}", t.label())))
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(if active { theme::panel_hi() } else { theme::panel() })
                    .text_xs()
                    .text_color(if active { theme::accent() } else { theme::muted() })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.tab = t;
                            cx.notify();
                        }),
                    )
                    .child(t.label()),
            );
        }
        row
    }

    /// The active right-pane workspace panel.
    fn workspace(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        match self.tab {
            Tab::Shell => self.shell_panel(cx).into_any_element(),
            Tab::Agent => self.agent_panel().into_any_element(),
            Tab::Swarm => self.swarm_panel(cx).into_any_element(),
            Tab::Graph => self.graph_panel().into_any_element(),
            Tab::Organs => self.organs_panel().into_any_element(),
            Tab::Proofs => self.proofs_panel().into_any_element(),
            Tab::Buffer => self.buffer_panel(cx).into_any_element(),
            Tab::Terminal => self.terminal_panel(cx).into_any_element(),
            Tab::Composer => self.composer(cx).into_any_element(),
            Tab::Objects => self.objects_panel().into_any_element(),
            Tab::Debugger => self.debugger_panel().into_any_element(),
            Tab::Replay => self.replay_panel().into_any_element(),
            Tab::Cipherclerk => self.cipherclerk_panel(cx).into_any_element(),
            Tab::Editor => self.editor_panel().into_any_element(),
        }
    }

    /// THE SHELL panel — the cap-first window manager / compositor. Composes the
    /// live [`Scene`] (surfaces over real cells, z-ordered) and renders each
    /// surface as a window with: a SHELL-DRAWN trusted-path identity header
    /// (anti-spoof — the owning cell id + lifecycle, read from the live ledger),
    /// the surface's own title, cap-gated window controls, and a body of the
    /// real cell's state. The whole compositor reacts to real turns (it re-reads
    /// the world each frame).
    fn shell_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let scene: Scene = self.shell.compose(&w);
        let layout = scene.layout;
        let focused = scene.focused;

        let mut col = div().flex().flex_col().gap_2().p_3().size_full();
        col = col.child(section_title("SHELL · cap-first compositor over real cells").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Each dregg CELL is a cap-confined SURFACE. Every window op (focus · close · \
             minimize) is GATED by the surface's capability — there is no ambient authority. \
             The identity badge on each surface is drawn by the SHELL from the live ledger \
             (anti-spoof), so a surface cannot impersonate another cell.",
        ));

        // The compositor toolbar: layout + the cap-gated ops.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(format!("layout: {}", layout.label()), theme::accent()))
                .child(pill(format!("{} surfaces", self.shell.surface_count()), theme::good()))
                .child(pill(format!("console s{}", self.console_surface.as_u64()), theme::warn()))
                .child(shell_button(cx, "open selected as surface", theme::good(), Cockpit::shell_open_selected))
                .child(shell_button(cx, "focus front", theme::accent(), Cockpit::shell_focus_front))
                .child(shell_button(cx, "minimize focused", theme::accent(), Cockpit::shell_minimize_focused))
                .child(shell_button(cx, "present focused (commits)", theme::good(), Cockpit::shell_present_focused))
                .child(shell_button(cx, "⚠ overpaint (T1 REJECT)", theme::warn(), Cockpit::shell_overpaint_focused))
                .child(shell_button(cx, "⚠ input-steal (T3 REJECT)", theme::warn(), Cockpit::shell_input_steal))
                .child(shell_button(cx, "share (read-only mirror)", theme::good(), Cockpit::shell_share_focused))
                .child(shell_button(cx, "⚠ over-share (watch it REJECT)", theme::warn(), Cockpit::shell_overshare_focused))
                .child(shell_button(cx, "close focused", theme::warn(), Cockpit::shell_close_focused))
                .child(shell_button(cx, "cycle layout", theme::accent(), Cockpit::shell_cycle_layout)),
        );
        col = col.child(self.outcome_banner());
        // The verified-scene legend: the three teeth the compositor enforces.
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Verified scene (the Lean Compositor AppSpec, on glass): T1 NON-OVERLAP — a surface \
             paints only its own cap-authorized region (overpaint REFUSED); T2 LABEL-BINDING — the \
             identity badge is a function of the owner + state-root the SHELL reads (spoof REFUSED); \
             T3 FOCUS-EXCLUSIVITY — input routes only to the one focused surface (steal REFUSED).",
        ));
        // The frame log: how many genuine presents have committed (provenance).
        col = col.child(
            div()
                .flex()
                .gap_1()
                .items_center()
                .child(pill(format!("{} frames committed", self.shell.frame_log().len()), theme::accent()))
                .child(div().text_xs().text_color(theme::muted()).child(
                    "each frame is a present that passed T1∧T2∧T3 (a refused present logs none — fail-closed)",
                )),
        );

        // The composed scene: surfaces front-to-back (front first, so the most
        // recently focused window reads at the top of the list).
        let mut stack = div().flex().flex_col().gap_2().mt_1();
        for item in scene.items.iter().rev() {
            let id = item.surface.id();
            let is_focused = focused == Some(id);
            let is_console = item.surface.is_console();
            let held_cap = self.surface_caps.contains_key(&id);

            // The trusted-path identity header — SHELL-drawn, from the ledger.
            let (badge_label, badge_color) = identity_badge(item.identity.lifecycle);
            let owner = if is_console {
                "SYSTEM (trusted root)".to_string()
            } else {
                format!("owner cell {}", item.identity.short)
            };

            // The window body: the real cell's live state (balance/nonce/caps/
            // lifecycle), read fresh from the ledger — never a mock.
            let body = self.surface_body(&item.surface.cell(), &w, is_console);

            let border = if is_focused { theme::accent() } else { theme::border() };
            stack = stack.child(
                div()
                    .id(SharedString::from(format!("surface-{}", id.as_u64())))
                    .flex()
                    .flex_col()
                    .rounded_md()
                    .border_1()
                    .border_color(border)
                    .bg(theme::panel())
                    .cursor_pointer()
                    // Clicking the surface is a HINT; the cap-gated focus is the
                    // authority (routed through `shell_click_surface`).
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.shell_click_surface(id, cx);
                        }),
                    )
                    // The title bar: identity badge (shell-drawn) + title + chrome.
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .items_center()
                            .px_2()
                            .py_1()
                            .rounded_md()
                            .bg(if is_focused { theme::panel_hi() } else { theme::panel() })
                            .border_b_1()
                            .border_color(theme::border())
                            .child(
                                div()
                                    .flex()
                                    .gap_2()
                                    .items_center()
                                    .child(div().text_xs().text_color(if is_console { theme::warn() } else { theme::accent() }).child(if is_console { "◆" } else { "⬡" }))
                                    .child(div().text_color(theme::text()).child(item.surface.title().to_string()))
                                    .child(pill(badge_label, badge_color)),
                            )
                            .child(
                                div()
                                    .flex()
                                    .gap_1()
                                    .items_center()
                                    .child(div().text_xs().text_color(theme::muted()).child(format!("z{}", item.surface.z())))
                                    .when(is_focused, |d| d.child(pill("focused", theme::good())))
                                    .when(item.surface.is_minimized(), |d| d.child(pill("min", theme::muted())))
                                    .when(!held_cap, |d| d.child(pill("no cap", theme::bad()))),
                            ),
                    )
                    // The trusted-path provenance line (anti-spoof): the owner the
                    // SHELL attests, plus whether the cell is backed in the ledger.
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .px_2()
                            .py_0p5()
                            .child(div().text_xs().text_color(theme::muted()).child(owner))
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(if item.identity.backed || is_console { theme::muted() } else { theme::bad() })
                                    .child(if is_console {
                                        "trusted-path: system console".to_string()
                                    } else if item.identity.backed {
                                        "trusted-path: shell-attested ✓".to_string()
                                    } else {
                                        "trusted-path: UNBACKED (cell missing)".to_string()
                                    }),
                            ),
                    )
                    // The body (the real cell's live state) — hidden when minimized.
                    .when(!item.surface.is_minimized(), |d| d.child(body)),
            );
        }
        col = col.child(stack);
        col
    }

    /// The body of a surface: the backing cell's LIVE state, read from the
    /// ledger. For the console it shows the image summary instead (it is the
    /// system's own root, not a single cell's view). Never a mock — this is the
    /// surface "reacting to real turns".
    fn surface_body(&self, cell: &CellId, w: &World, is_console: bool) -> gpui::AnyElement {
        let mut body = div().flex().flex_col().gap_0p5().px_2().py_1();
        if is_console {
            body = body
                .child(div().text_xs().text_color(theme::muted()).child(format!(
                    "image · {} cells · h{} · {} receipts",
                    w.cell_count(),
                    w.height(),
                    w.receipts().len()
                )))
                .child(div().text_xs().text_color(theme::accent()).child(format!(
                    "root {}",
                    reflect::short_hex(&w.state_root())
                )));
            return body.into_any_element();
        }
        match w.ledger().get(cell) {
            Some(c) => {
                let bal = c.state.balance();
                let bal_color = if bal < 0 { theme::warn() } else { theme::text() };
                body = body
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("balance"))
                            .child(div().text_xs().text_color(bal_color).child(format!("{bal}"))),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("nonce"))
                            .child(div().text_xs().text_color(theme::text()).child(format!("{}", c.state.nonce()))),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("capabilities"))
                            .child(div().text_xs().text_color(theme::text()).child(format!("{}", c.capabilities.len()))),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("lifecycle"))
                            .child(div().text_xs().text_color(theme::text()).child(format!("{:?}", c.lifecycle))),
                    );
            }
            None => {
                body = body.child(
                    div()
                        .text_xs()
                        .text_color(theme::bad())
                        .child("(backing cell is not in the ledger — a dangling surface)"),
                );
            }
        }
        body.into_any_element()
    }

    /// THE AGENT-ACTIVITY panel — the ADOS keystone. Renders an agent loop's
    /// PROVABLE activity as a cap-gated surface cell: its held mandate (the
    /// attenuated authority it runs under), its recent cap-gated turns + their
    /// receipts (the grounded seam, read from the embedded World's receipt log +
    /// dynamics stream), and the legible boundary of what it is authorized to do.
    /// Maps `agent::AgentActivity` (gpui-free) onto gpui — you watch the
    /// executor's receipts, not the agent's self-report.
    fn agent_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let act = self.agent_surface.activity(&w, 24);

        let mut col = div().flex().flex_col().gap_2().p_3().size_full();
        col = col.child(section_title("AGENT · the grounded loop (provable activity as a surface)").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "An agent is an intricate LOOP; dregg grounds the ONE seam that matters — its ACTIONS, \
             at the tool-call/turn boundary — by making every action a cap-gated, RECEIPTED, \
             conservation-checked turn. This surface renders that seam: the mandate it holds, the \
             turns it committed (with receipts), and the boundary of what it may do. You watch the \
             executor's truth, never the agent's self-report.",
        ));

        // The agent header: who it is + its live resources + grounded step count.
        let backed_color = if act.backed { theme::good() } else { theme::bad() };
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(format!("agent {}", act.short), theme::accent()))
                .child(pill(
                    if act.backed { "live" } else { "UNBACKED" }.to_string(),
                    backed_color,
                ))
                .child(pill(format!("balance {}", act.balance), theme::text()))
                .child(pill(format!("{} committed turns", act.committed_action_count()), theme::good()))
                .child(pill(format!("reach {} cell(s)", act.reach()), theme::accent()))
                .child(pill(format!("nonce {}", act.nonce), theme::muted())),
        );

        // --- THE HELD MANDATE (the attenuated authority the loop runs under) ---
        col = col.child(section_title("held mandate (adoption = attenuation)").mt_2());
        if act.mandate.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "holds NO outbound capability — this agent is confined to itself (the narrowest mandate).",
            ));
        } else {
            let mut edges = div().flex().flex_col().gap_0p5();
            for m in &act.mandate {
                let rights_color = match m.rights_label() {
                    "open" => theme::warn(),
                    "locked" => theme::bad(),
                    _ => theme::good(),
                };
                edges = edges.child(
                    div()
                        .flex()
                        .justify_between()
                        .items_center()
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel())
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(theme::muted()).child(format!("slot {}", m.slot)))
                                .child(div().text_xs().text_color(theme::text()).child(format!(
                                    "→ {}",
                                    reflect::short_hex(m.target.as_bytes())
                                )))
                                .child(pill(m.rights_label(), rights_color)),
                        )
                        .child(
                            div()
                                .flex()
                                .gap_1()
                                .items_center()
                                .when(m.faceted, |d| d.child(pill("faceted", theme::accent())))
                                .when(m.expires_at.is_some(), |d| {
                                    d.child(pill(format!("expires @{}", m.expires_at.unwrap()), theme::warn()))
                                }),
                        ),
                );
            }
            col = col.child(edges);
        }

        // --- THE CAP-GATED ACTIONS (turns) + their RECEIPTS (the grounded seam) ---
        col = col.child(section_title("recent cap-gated actions (turns + receipts)").mt_2());
        if act.actions.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "no actions yet — this agent's loop has not committed (or attempted) a turn.",
            ));
        } else {
            let mut rows = div().flex().flex_col().gap_0p5();
            for a in &act.actions {
                let (mark, mark_color) = if a.committed {
                    ("✓", theme::good())
                } else {
                    ("✗", theme::bad())
                };
                let height_label = a
                    .height
                    .map(|h| format!("h{h}"))
                    .unwrap_or_else(|| "—".to_string());
                rows = rows.child(
                    div()
                        .flex()
                        .justify_between()
                        .items_center()
                        .px_2()
                        .py_0p5()
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(mark_color).child(mark))
                                .child(div().text_xs().text_color(theme::muted()).child(height_label))
                                .child(div().text_xs().text_color(if a.committed { theme::text() } else { theme::bad() }).child(a.summary.clone())),
                        )
                        .child(
                            div()
                                .flex()
                                .gap_1()
                                .items_center()
                                .when(a.committed, |d| {
                                    d.child(div().text_xs().text_color(theme::muted()).child(format!("{} act · {} ⚙", a.action_count, a.computrons)))
                                })
                                .when(a.receipt_hash.is_some(), |d| {
                                    d.child(pill(reflect::short_hex(&a.receipt_hash.unwrap()), theme::good()))
                                }),
                        ),
                );
            }
            col = col.child(rows);
        }

        // --- WHAT IT IS AUTHORIZED TO DO (the boundary of the loop's reach) ---
        col = col.child(section_title("what it is authorized to do (the boundary)").mt_2());
        let mut auths = div().flex().flex_col().gap_0p5();
        for a in &act.authorizations {
            let (mark, mark_color) = if a.permitted {
                ("CAN", theme::good())
            } else {
                ("CANNOT", theme::bad())
            };
            auths = auths.child(
                div()
                    .flex()
                    .justify_between()
                    .items_center()
                    .px_2()
                    .py_0p5()
                    .child(
                        div()
                            .flex()
                            .gap_2()
                            .items_center()
                            .child(pill(mark, mark_color))
                            .child(div().text_xs().text_color(theme::text()).child(a.verb)),
                    )
                    .child(div().text_xs().text_color(theme::muted()).child(a.note.clone())),
            );
        }
        col = col.child(auths);
        col
    }

    /// THE A2 SWARM PANEL — multi-agent cap-coordination surface.
    ///
    /// Renders the [`SwarmView`]: each member's mandate + action count + inbox,
    /// the inter-member notify-edge activity feed, and the demo action row
    /// (emit a wake / drain the inbox / transfer-and-wake in one turn).
    ///
    /// The point: you watch the EXECUTOR's receipts for each member's committed
    /// turns, and the INBOX accumulates pending wakes from peers' emits — all
    /// on-ledger truth, never a self-report. The async model (send ≠ receive)
    /// is visible: the coordinator's emit receipt and worker-a's drain receipt
    /// are DIFFERENT turns with DIFFERENT heights.
    fn swarm_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let view = SwarmView::build(&self.swarm, &w);
        drop(w);

        let mut col = div().flex().flex_col().gap_2().p_3().size_full();
        col = col.child(section_title("SWARM (A2) · multi-agent cap-coordination · notify-edge inbox").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "N agent cells coordinating as confined Surface cells. Every action is a cap-gated, \
             receipted turn at the ONE seam. An EmitEvent deposits a NotifyEdge in the \
             recipient's inbox; the recipient drains it in its OWN separate future turn \
             (async — not a joint turn). You watch the executor's truth, never a self-report.",
        ));

        // Header: swarm stats.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(format!("{} members", view.members.len()), theme::accent()))
                .child(pill(format!("{} total actions", view.total_actions), theme::good()))
                .child(pill(
                    format!("{} pending wakes", view.total_pending),
                    if view.total_pending > 0 { theme::warn() } else { theme::muted() },
                )),
        );

        // Members: one row per member.
        col = col.child(section_title("members (cap-confined, mandate-gated)").mt_2());
        let mut members_col = div().flex().flex_col().gap_1();
        for m in &view.members {
            let backed_color = if m.backed { theme::good() } else { theme::bad() };
            let inbox_color = if m.pending_notify > 0 { theme::warn() } else { theme::muted() };
            members_col = members_col.child(
                div()
                    .flex()
                    .flex_col()
                    .gap_0p5()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(theme::panel())
                    .child(
                        div()
                            .flex()
                            .gap_1()
                            .items_center()
                            .child(pill(m.name.clone(), theme::accent()))
                            .child(pill(m.short.clone(), theme::muted()))
                            .child(pill(if m.backed { "live" } else { "UNBACKED" }, backed_color))
                            .child(pill(format!("bal {}", m.balance), theme::text()))
                            .child(pill(format!("{} actions", m.action_count), theme::good()))
                            .child(pill(
                                format!("{} pending", m.pending_notify),
                                inbox_color,
                            )),
                    )
                    .when(!m.inbox.is_empty(), |d| {
                        let mut inbox_div = div().flex().flex_col().gap_0p5().mt_1();
                        for n in &m.inbox {
                            let (mark, color) = if n.drained {
                                ("✓", theme::muted())
                            } else {
                                ("⚡", theme::warn())
                            };
                            inbox_div = inbox_div.child(
                                div()
                                    .flex()
                                    .gap_1()
                                    .items_center()
                                    .text_xs()
                                    .px_2()
                                    .child(div().text_color(color).child(mark))
                                    .child(
                                        div()
                                            .text_color(if n.drained { theme::muted() } else { theme::text() })
                                            .child(n.label()),
                                    ),
                            );
                        }
                        d.child(inbox_div)
                    }),
            );
        }
        col = col.child(members_col);

        // Action row: the demo verbs.
        col = col.child(section_title("demo actions (the A2 seam)").mt_2());
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(verb_button(cx, "coordinator emit task/go → worker-a", theme::accent(), Cockpit::swarm_coordinator_emit_a))
                .child(verb_button(cx, "worker-a DRAIN inbox (own ack turn)", theme::good(), Cockpit::swarm_worker_a_drain))
                .child(verb_button(cx, "coordinator: transfer + wake (one seam)", theme::warn(), Cockpit::swarm_coordinator_transfer_and_wake)),
        );

        // Activity feed: recent swarm actions (newest-first).
        col = col.child(section_title("activity feed (executor receipts · notify edges)").mt_2());
        if view.activity.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "no swarm actions yet — use the buttons above to run the first turns.",
            ));
        } else {
            let mut feed = div().flex().flex_col().gap_0p5();
            for entry in &view.activity {
                let (mark, mark_color) = if entry.committed {
                    ("✓", theme::good())
                } else {
                    ("✗", theme::bad())
                };
                let height_label = entry.height.map(|h| format!("h{h}")).unwrap_or_else(|| "—".to_string());
                let receipt_label = entry.receipt_short.as_deref().unwrap_or("—");
                feed = feed.child(
                    div()
                        .flex()
                        .flex_col()
                        .gap_0p5()
                        .px_2()
                        .py_0p5()
                        .rounded_sm()
                        .bg(theme::panel())
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(mark_color).child(mark))
                                .child(div().text_xs().text_color(theme::muted()).child(height_label))
                                .child(div().text_xs().text_color(theme::accent()).child(entry.member_short.clone()))
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(if entry.committed { theme::text() } else { theme::bad() })
                                        .child(entry.summary.clone()),
                                )
                                .when(entry.committed, |d| {
                                    d.child(pill(receipt_label.to_string(), theme::good()))
                                }),
                        )
                        .when(!entry.notify_edges.is_empty(), |d| {
                            let mut edges_div = div().flex().flex_col().gap_0p5().px_2();
                            for edge_label in &entry.notify_edges {
                                edges_div = edges_div.child(
                                    div()
                                        .text_xs()
                                        .text_color(theme::warn())
                                        .child(format!("  ⚡ {edge_label}")),
                                );
                            }
                            d.child(edges_div)
                        }),
                );
            }
            col = col.child(feed);
        }

        col
    }

    /// THE TURN DEBUGGER panel — maps `debug::render`'s gpui-free model onto
    /// gpui elements (step list, conservation Σδ, the refusal explanation).
    fn debugger_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let panel = debug::render(&w, &self.debug_turn, &self.breakpoints);

        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("DEBUGGER · step · inspect · explain").mb_1());
        col = col.child(div().text_color(theme::text()).child(panel.title.clone()));
        col = col.child(div().text_xs().text_color(theme::muted()).mb_2().child(panel.subtitle.clone()));

        // The step list.
        let mut steps = div().flex().flex_col().gap_0p5();
        for s in &panel.steps {
            let color = if !s.committed {
                theme::bad()
            } else if s.is_break {
                theme::warn()
            } else {
                theme::text()
            };
            steps = steps.child(
                div()
                    .flex()
                    .justify_between()
                    .px_2()
                    .child(div().text_xs().text_color(color).child(format!(
                        "{} k{} {}",
                        if s.is_break { "◆" } else { "·" },
                        s.index,
                        s.label
                    )))
                    .child(div().text_xs().text_color(theme::muted()).child(format!("Σδ={}", s.conservation_delta))),
            );
        }
        col = col.child(steps);

        // The refusal explanation (the prize) or the conserving commit line.
        col = col.child(match &panel.refusal {
            Some(r) => div()
                .mt_2()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .flex()
                .flex_col()
                .gap_0p5()
                .child(div().text_xs().text_color(theme::bad()).child(format!("REFUSED · guard: {}", r.guard)))
                .child(div().text_xs().text_color(theme::text()).child(r.headline.clone()))
                .child(div().text_xs().text_color(theme::muted()).child(r.detail.clone())),
            None => div()
                .mt_2()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(theme::good())
                .child(format!("COMMITS · final Σδ = {} (conserves)", panel.final_conservation_delta)),
        });
        col
    }

    /// THE REPLAY / TIME-TRAVEL panel — `replay::replay_panel` returns gpui
    /// directly; the cockpit owns the cursor + any pinned fork and rebuilds the
    /// model each frame from the live world's REAL history.
    fn replay_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let history = w.recorded_turns();
        let cursor = self.replay_cursor.min(history.len());
        let model = replay::ReplayPanelModel::build(history, cursor, self.replay_fork.as_ref());
        div()
            .flex()
            .flex_col()
            .size_full()
            .child(replay::replay_panel(&model))
    }

    /// THE CIPHERCLERK panel — maps `cipherclerk::render`'s reflective lists
    /// onto the cockpit's shared inspector rows.
    fn cipherclerk_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let panel = cipherclerk::render(&self.clerk);
        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("CIPHERCLERK · identities · tokens · delegations").mb_1());

        // The REAL macaroon action loop (mint → attenuate → delegate → discharge),
        // each driving `AgentCipherclerk`. Acts on alice (the holder) + bob (the
        // delegatee) over the "dns" service.
        col = col.child(div().text_xs().text_color(theme::muted()).child("ACTIONS (alice · service 'dns')"));
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(clerk_button(cx, "mint root", theme::good(), Cockpit::run_clerk_mint))
                .child(clerk_button(cx, "attenuate → r", theme::accent(), Cockpit::run_clerk_attenuate))
                .child(clerk_button(cx, "delegate → bob", theme::accent(), Cockpit::run_clerk_delegate))
                .child(clerk_button(cx, "discharge (verify)", theme::warn(), Cockpit::run_clerk_discharge)),
        );
        // The real action result banner.
        col = col.child(self.clerk_banner());

        col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("IDENTITIES"));
        for ins in &panel.identities {
            col = col.child(inspectable_row(ins));
        }
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("HELD TOKENS"));
        if panel.tokens.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(none minted yet)"));
        }
        for ins in &panel.tokens {
            col = col.child(inspectable_row(ins));
        }
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("DELEGATIONS"));
        if panel.delegations.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(none recorded)"));
        }
        for ins in &panel.delegations {
            col = col.child(inspectable_row(ins));
        }
        col
    }

    /// The cipherclerk action result banner (the real mint/attenuate/delegate/
    /// discharge outcome). Colors a denied discharge or a failure red.
    fn clerk_banner(&self) -> impl IntoElement {
        let (txt, color) = match &self.clerk_outcome {
            None => ("(run a clerk action above)".to_string(), theme::muted()),
            Some(o) => {
                let denied = matches!(
                    o,
                    cipherclerk::ClerkOutcome::Discharged { authorized: false, .. }
                );
                let color = if !o.is_ok() || denied {
                    theme::bad()
                } else {
                    theme::good()
                };
                (o.banner(), color)
            }
        };
        div()
            .mt_1()
            .mb_1()
            .p_2()
            .rounded_md()
            .bg(theme::panel())
            .text_xs()
            .text_color(color)
            .child(txt)
    }

    /// THE OBJECTS panel — the reflective object views over the protocol
    /// surface beyond cells/receipts: each committed turn's PROOF / STARK status,
    /// the NULLIFIERS (consumed one-time authorities) it spent, and the
    /// lifecycle of every cell (live / sealed / destroyed). All projected through
    /// `reflect` from the live world — never a parallel schema.
    fn objects_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("OBJECTS · proofs · nullifiers · lifecycle").mb_1());

        // Lifecycle column: every cell's lifecycle state (the seal/destroy axis).
        col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("CELL LIFECYCLE"));
        for id in &self.cells {
            if let Some(cell) = w.ledger().get(id) {
                let (label, color) = lifecycle_badge(&cell.lifecycle);
                col = col.child(
                    div()
                        .flex()
                        .justify_between()
                        .px_2()
                        .py_0p5()
                        .child(div().text_xs().text_color(theme::text()).child(format!("⬡ {}", reflect::short_hex(id.as_bytes()))))
                        .child(div().text_xs().text_color(color).child(label)),
                );
            }
        }

        // Proof status + nullifiers for the most recent receipts.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("TURN PROOFS (most recent)"));
        if w.receipts().is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no turns yet)"));
        }
        for r in w.receipts().iter().rev().take(6) {
            let proof = reflect::reflect_proof_status(r);
            col = col.child(inspectable_row(&proof));
            for null in reflect::reflect_nullifiers(r) {
                col = col.child(inspectable_row(&null));
            }
        }
        col
    }

    /// THE GRAPH panel — the whole-graph ocap delegation layout. Renders the
    /// capability graph as nodes (cells, with in/out degree) + edges (grants,
    /// with rights), and — rooted on the first source cell — the LAYERED
    /// multi-hop delegation depth (root at depth 0, its grantees at depth 1, …)
    /// plus each source's transitive blast radius. The View tree IS the ocap
    /// graph (`starbridge_v2::graph`).
    fn graph_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let g = starbridge_v2::graph::OcapGraph::build(&w);
        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("GRAPH · ocap delegation (multi-hop)").mb_1());
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(format!(
                "{} cells · {} capability edges",
                g.node_count(),
                g.edge_count()
            )),
        );

        // The EDGES — the literal ocap graph (holder ──rights──▶ target).
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("CAPABILITY EDGES"));
        if g.edge_count() == 0 {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no capability edges yet)"));
        }
        for e in g.edges().iter().take(24) {
            let deleg = if e.is_delegated() { " · delegated" } else { "" };
            let facet = if e.faceted { " · faceted" } else { "" };
            col = col.child(
                div()
                    .flex()
                    .justify_between()
                    .px_2()
                    .py_0p5()
                    .child(
                        div().text_xs().text_color(theme::text()).child(format!(
                            "⬡ {} ──▶ {}",
                            reflect::short_hex(e.holder.as_bytes()),
                            reflect::short_hex(e.target.as_bytes()),
                        )),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::accent())
                            .child(format!("[{}]{deleg}{facet}", e.rights_label())),
                    ),
            );
        }

        // The LAYERED multi-hop layout, rooted on each source cell (no inbound
        // edge — the authority origins), with the transitive blast radius.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("MULTI-HOP LAYOUT (by delegation depth)"));
        let roots = g.source_roots();
        if roots.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no source root — the graph may be cyclic)"));
        }
        for root in roots.iter().take(4) {
            let reach = g.reach_count(root);
            col = col.child(
                div().text_xs().text_color(theme::good()).px_2().mt_1().child(format!(
                    "root {} · reaches {} cell(s) transitively{}",
                    reflect::short_hex(root.as_bytes()),
                    reach,
                    if g.has_cycle_from(root) { " · ⟳ cyclic" } else { "" },
                )),
            );
            for layer in g.layered_from(root) {
                if layer.cells.is_empty() {
                    continue;
                }
                let cells: Vec<String> = layer
                    .cells
                    .iter()
                    .map(|c| reflect::short_hex(c.as_bytes()))
                    .collect();
                col = col.child(
                    div().text_xs().text_color(theme::text()).px_3().child(format!(
                        "depth {}: {}",
                        layer.depth,
                        cells.join(", ")
                    )),
                );
            }
        }
        col
    }

    /// THE ORGANS panel — reflects each dregg organ's live cell-state. Trustline
    /// and flash-well organs are LIVE (embed-core: their enforcement is the cell's
    /// executor-installed program, fully readable from the embedded ledger);
    /// channel / mailbox / court are surfaced HONESTLY as remote-path (behind
    /// captp). See [`starbridge_v2::organs`].
    fn organs_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let survey = starbridge_v2::organs::OrganSurvey::build(&w);
        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("ORGANS · live organ cell-state").mb_1());
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(format!(
                "{} live organ(s) (embed-core) · {} remote-path",
                survey.live_count(),
                survey.remote.len()
            )),
        );

        // LIVE trustline organs.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("TRUSTLINES (live)"));
        if survey.trustlines.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no trustline organ in the world)"));
        }
        for t in &survey.trustlines {
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(div().text_xs().text_color(theme::text()).child(format!("⬡ {} (trustline)", t.short)))
                    .child(div().text_xs().text_color(theme::accent()).child(t.summary())),
            );
        }

        // LIVE flash-well organs.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("FLASH WELLS (live)"));
        if survey.flash_wells.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no flash-well organ in the world)"));
        }
        for f in &survey.flash_wells {
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(div().text_xs().text_color(theme::text()).child(format!("⬡ {} (flash well)", f.short)))
                    .child(div().text_xs().text_color(theme::accent()).child(f.summary())),
            );
        }

        // REMOTE-PATH organs (honest — kind + seam + route, not faked state).
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("REMOTE-PATH ORGANS (need a connected node)"));
        for o in &survey.remote {
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(div().text_xs().text_color(theme::warn()).child(format!("⬡ {} — remote-path", o.kind)))
                    .child(div().text_xs().text_color(theme::muted()).child(o.seam.to_string())),
            );
        }
        col
    }

    /// THE PROOFS panel — the proof-attach + STARK verification-status board.
    /// Each committed turn's verification tier (verified-by-construction /
    /// executor-signed / STARK-attached) + the honest route to the next tier.
    /// See [`starbridge_v2::proofs`].
    fn proofs_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let board = starbridge_v2::proofs::ProofBoard::build(&w, 16);
        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("PROOFS · attach + STARK verification status").mb_1());
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(format!(
                "{} verified-by-construction · {} signed · {} STARK-attached",
                board.by_construction, board.signed, board.stark_attached
            )),
        );
        if board.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().mt_1().child("(no committed turns yet)"));
        }
        for e in &board.entries {
            let tier_color = match e.tier {
                starbridge_v2::proofs::VerificationTier::StarkAttached => theme::good(),
                starbridge_v2::proofs::VerificationTier::ExecutorSigned => theme::accent(),
                starbridge_v2::proofs::VerificationTier::VerifiedByConstruction => theme::text(),
            };
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(
                        div().flex().justify_between()
                            .child(div().text_xs().text_color(theme::text()).child(format!("h{} · {}", e.height, e.receipt_short)))
                            .child(div().text_xs().text_color(tier_color).child(e.tier.label())),
                    )
                    .child(div().text_xs().text_color(theme::muted()).child(e.summary())),
            );
            if let Some(route) = e.upgrade_route() {
                col = col.child(div().text_xs().text_color(theme::muted()).px_3().child(format!("→ next: {route}")));
            }
        }
        col
    }

    /// THE ⌘K COMMAND PALETTE overlay — a centered, fuzzy-filtered list over
    /// EVERY action. Rendered on top of the cockpit when open. The query +
    /// selection live in `self.palette`; keystrokes are handled in [`on_key`];
    /// a click on a row also dispatches it.
    fn palette_overlay(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let results = self.palette.results();
        let selected = self.palette.selected();
        let query = self.palette.query().to_string();

        // A full-screen scrim that closes the palette on a click-out.
        let scrim = div()
            .id("palette-scrim")
            .absolute()
            .top_0()
            .left_0()
            .size_full()
            .bg(gpui::rgba(0x00000088))
            .flex()
            .flex_col()
            .items_center()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|this, _ev, _w, cx| {
                    this.palette.close();
                    cx.notify();
                }),
            );

        // The palette card.
        let mut card = div()
            .id("palette-card")
            .mt(px(120.))
            .w(px(560.))
            .max_h(px(440.))
            .flex()
            .flex_col()
            .rounded_md()
            .border_1()
            .border_color(theme::accent())
            .bg(theme::panel())
            // Swallow clicks on the card so they don't reach the scrim's close.
            .on_mouse_down(MouseButton::Left, |_ev, _w, cx| cx.stop_propagation());

        // The query line.
        card = card.child(
            div()
                .flex()
                .justify_between()
                .px_3()
                .py_2()
                .border_b_1()
                .border_color(theme::border())
                .child(
                    div()
                        .text_color(theme::text())
                        .child(if query.is_empty() {
                            "⌘K  type to search every action…".to_string()
                        } else {
                            format!("⌘K  {query}▌")
                        }),
                )
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(format!("{} match", results.len())),
                ),
        );

        // The results list.
        let mut list = div().flex().flex_col().gap_0p5().p_1().overflow_hidden();
        if results.is_empty() {
            list = list.child(
                div()
                    .px_2()
                    .py_1()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("(no matching action — Esc to close)"),
            );
        }
        for (i, hit) in results.iter().enumerate().take(12) {
            let active = i == selected;
            let (badge, bcolor) = category_badge(hit.command.category);
            let id = hit.command.id;
            list = list.child(
                div()
                    .id(SharedString::from(format!("palette-row-{i}")))
                    .flex()
                    .justify_between()
                    .items_center()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(if active { theme::panel_hi() } else { theme::panel() })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.palette.close();
                            this.dispatch(id, cx);
                            cx.notify();
                        }),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(if active { theme::accent() } else { theme::text() })
                            .child(format!("{} {}", if active { "▸" } else { " " }, hit.command.title)),
                    )
                    .child(pill(badge, bcolor)),
            );
        }
        card = card.child(list);

        // Footer hint.
        card = card.child(
            div()
                .px_3()
                .py_1()
                .border_t_1()
                .border_color(theme::border())
                .text_xs()
                .text_color(theme::muted())
                .child("↑↓ select · ⏎ run · esc close"),
        );

        scrim.child(card)
    }

    /// THE A1 EDITOR/BUFFER panel — a text buffer as a cap-confined Surface cell.
    /// Maps `buffer::BufferView` (gpui-free) onto gpui: the buffer header (its
    /// backing cell, revision, read-only/dirty badges, digests), the cap-gated
    /// action row (type · commit · the read-only-write REFUSE teaching moment),
    /// and the buffer body (the editable text, with line numbers). You watch the
    /// authenticated digest advance through a verified turn — not a self-report.
    fn buffer_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let v = BufferView::build(&self.editor_buffer, &w, Some(&self.editor_buffer_cap));
        drop(w);

        let mut col = div().flex().flex_col().gap_2().p_3().size_full();
        col = col.child(section_title("EDITOR · a text buffer as a cap-confined Surface cell").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The buffer is backed by a REAL cell: its content DIGEST rides the cell's state, and \
             its REVISION is the cell's nonce. Editing the text is free (in-memory); COMMITTING is \
             a CAP-GATED verified turn (a SetField writing the digest). A read-only buffer holds an \
             ATTENUATED cap — a write to it REFUSES (no-amplification at the editor).",
        ));

        // The buffer header: backing cell, state, badges, digests.
        let backed_color = if v.backed { theme::good() } else { theme::bad() };
        let rw_badge = if v.read_only { ("read-only", theme::warn()) } else { ("writable", theme::good()) };
        let clean_badge = if v.clean { ("clean", theme::good()) } else { ("DIRTY (unsaved)", theme::warn()) };
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(v.name.clone(), theme::accent()))
                .child(pill(format!("cell {}", v.backing_short), theme::text()))
                .child(pill(if v.backed { "live" } else { "UNBACKED" }.to_string(), backed_color))
                .child(pill(rw_badge.0, rw_badge.1))
                .child(pill(clean_badge.0, clean_badge.1))
                .child(pill(format!("rev {}", v.revision), theme::muted())),
        );
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child("doc digest"))
                .child(pill(v.doc_digest_short.clone(), theme::accent()))
                .when(v.stored_digest_short.is_some(), |d| {
                    d.child(div().text_xs().text_color(theme::muted()).child("committed"))
                        .child(pill(v.stored_digest_short.clone().unwrap(), theme::good()))
                }),
        );

        // The cap-gated action row.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .mt_1()
                .child(shell_button(cx, "type a line", theme::accent(), Cockpit::buffer_type_demo))
                .child(shell_button(cx, "commit (cap-gated turn)", theme::good(), Cockpit::buffer_commit))
                .child(shell_button(cx, "⚠ read-only write (REFUSE)", theme::warn(), Cockpit::buffer_readonly_write_demo)),
        );

        // The buffer body: the editable text with line numbers.
        col = col.child(section_title("buffer (the surface content)").mt_2());
        let mut body = div().flex().flex_col().gap_0p5().p_2().rounded_md().bg(theme::panel());
        for (i, line) in v.lines.iter().enumerate() {
            body = body.child(
                div()
                    .flex()
                    .gap_2()
                    .child(div().text_xs().text_color(theme::muted()).w(px(28.)).child(format!("{:>3}", i + 1)))
                    .child(div().text_xs().text_color(theme::text()).font_family("monospace").child(line.clone())),
            );
        }
        col = col.child(body);
        col = col.child(
            div().text_xs().text_color(theme::muted()).mt_1().child(format!(
                "cursor @ byte {} · {} line(s) — the digest above is what a COMMIT would bind into the cell",
                v.cursor,
                v.lines.len()
            )),
        );
        col
    }

    /// THE A1 TERMINAL panel — a command surface as a cap-confined Surface cell
    /// (the home of the ADOS tool-call seam). Maps `terminal::TerminalView`
    /// (gpui-free) onto gpui: the terminal header (its backing cell + its
    /// MANDATE — the targets it may reach), the cap-gated action row (an
    /// in-mandate command COMMITS; an out-of-mandate one REFUSES), and the output
    /// body (each command + its REAL receipt, or its REFUSAL — never faked).
    fn terminal_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let v = TerminalView::build(&self.terminal, &w);
        drop(w);

        let mut col = div().flex().flex_col().gap_2().p_3().size_full();
        col = col.child(section_title("TERMINAL · a command surface as a cap-confined Surface cell").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "A command is a CAP-GATED action: the terminal-cell holds the cap for what it may run / \
             touch, and the output is its receipt. This is WHERE THE ADOS TOOL-CALL SEAM LIVES — an \
             agent's Bash routed through the terminal-cell's cap. A command whose target is within \
             the cell's mandate COMMITS (its receipt is the output); one outside it REFUSES.",
        ));

        // The terminal header: backing cell + the mandate (reachable targets).
        let backed_color = if v.backed { theme::good() } else { theme::bad() };
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(v.name.clone(), theme::accent()))
                .child(pill(format!("cell {}", v.backing_short), theme::text()))
                .child(pill(if v.backed { "live" } else { "UNBACKED" }.to_string(), backed_color))
                .child(pill(format!("{} committed", v.committed_count), theme::good())),
        );
        col = col.child(section_title("mandate — the targets this terminal may reach").mt_1());
        let mut mandate = div().flex().flex_wrap().gap_1().items_center();
        for t in &v.reachable_short {
            mandate = mandate.child(pill(format!("→ {t}"), theme::accent()));
        }
        col = col.child(mandate);

        // The cap-gated action row.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .mt_1()
                .child(shell_button(cx, "run in-mandate (COMMITS)", theme::good(), Cockpit::terminal_run_in_mandate))
                .child(shell_button(cx, "⚠ run out-of-mandate (REFUSE)", theme::warn(), Cockpit::terminal_run_out_of_mandate)),
        );

        // The output body: commands + receipts / refusals (oldest-first).
        col = col.child(section_title("output (commands + receipts — the surface content)").mt_2());
        if v.lines.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "no commands yet — run one above; an in-mandate target COMMITS, an out-of-mandate one REFUSES.",
            ));
        } else {
            let mut body = div().flex().flex_col().gap_0p5();
            for l in &v.lines {
                let (mark, mark_color) = if l.committed { ("$", theme::good()) } else { ("✗", theme::bad()) };
                body = body.child(
                    div()
                        .flex()
                        .flex_col()
                        .gap_0p5()
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel())
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(mark_color).child(mark))
                                .child(div().text_xs().text_color(theme::text()).font_family("monospace").child(l.command.clone()))
                                .when(l.committed, |d| {
                                    d.child(pill(format!("{} ⚙", l.computrons), theme::muted()))
                                })
                                .when(l.receipt_short().is_some(), |d| {
                                    d.child(pill(l.receipt_short().unwrap(), theme::good()))
                                }),
                        )
                        .child(
                            div()
                                .text_xs()
                                .text_color(if l.committed { theme::muted() } else { theme::bad() })
                                .font_family("monospace")
                                .child(l.result.clone()),
                        ),
                );
            }
            col = col.child(body);
        }
        col
    }

    /// THE LIVE EDITOR panel — `edit::render_panel` is gpui-free text; the
    /// cockpit presents it line-by-line.
    fn editor_panel(&self) -> impl IntoElement {
        let text = edit::render_panel(&self.editor);
        let mut col = div().flex().flex_col().p_3().size_full();
        col = col.child(section_title("LIVE EDITOR · author · validate · deploy").mb_1());
        for line in text.lines() {
            col = col.child(div().text_xs().text_color(theme::text()).font_family("monospace").child(line.to_string()));
        }
        col
    }
}

impl Render for Cockpit {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let palette_open = self.palette.is_open();
        div()
            .id("cockpit-root")
            .track_focus(&self.focus)
            .key_context("Cockpit")
            // ⌘K + the palette's typing/selection all flow through one handler.
            .on_key_down(cx.listener(|this, ev: &KeyDownEvent, _w, cx| {
                this.on_key(ev, cx);
            }))
            .relative()
            .flex()
            .size_full()
            .bg(theme::bg())
            .text_color(theme::text())
            .font_family("monospace")
            // Left rail: image header + cell world + dynamics feed.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .w(px(320.))
                    .h_full()
                    .border_r_1()
                    .border_color(theme::border())
                    .bg(theme::panel())
                    .child(self.rail_header())
                    .child(div().flex_1().child(self.cell_world(cx)))
                    .child(
                        div()
                            .border_t_1()
                            .border_color(theme::border())
                            .child(self.dynamics_feed()),
                    ),
            )
            // Center: inspector over blocklace.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .w(px(460.))
                    .h_full()
                    .border_r_1()
                    .border_color(theme::border())
                    .child(div().flex_1().child(self.inspector()))
                    .child(
                        div()
                            .h(px(260.))
                            .border_t_1()
                            .border_color(theme::border())
                            .bg(theme::panel())
                            .child(self.blocklace(cx)),
                    ),
            )
            // Right: the workspace — tab bar over the active feature panel
            // (composer · debugger · replay · cipherclerk · editor).
            .child(
                div()
                    .flex()
                    .flex_col()
                    .flex_1()
                    .h_full()
                    .child(self.tab_bar(cx))
                    .child(div().flex_1().overflow_hidden().child(self.workspace(cx))),
            )
            // THE ⌘K COMMAND PALETTE overlay (absolute, on top) when open.
            .when(palette_open, |root| root.child(self.palette_overlay(cx)))
    }
}

// --- small render helpers ---------------------------------------------------

fn sorted_cells(w: &World) -> Vec<CellId> {
    let mut ids: Vec<CellId> = w.ledger().iter().map(|(id, _)| *id).collect();
    ids.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    ids
}

/// A human reason for a refused shell op (the window-manager ocap guarantee
/// firing). Surfaced in the outcome banner the same way the executor's
/// rejections are — a refusal is a feature, not an error to hide.
fn shell_err(e: &starbridge_v2::shell::ShellError) -> String {
    use starbridge_v2::shell::ShellError;
    match e {
        ShellError::Unauthorized => "no valid capability presented (no ambient authority)".to_string(),
        ShellError::NoSuchSurface(id) => format!("surface {} does not exist", id.as_u64()),
        ShellError::ConsoleProtected => "the system console is the trusted root (cannot close)".to_string(),
        ShellError::ShareDenied(why) => format!("widening share refused by the executor: {why}"),
        // The verified-scene tooth that bit (T1 overpaint / T2 spoof / T3
        // misroute|double-focus), surfaced for the operator log.
        ShellError::PresentRefused(p) => p.explain(),
    }
}

fn kind_badge(kind: ObjectKind) -> impl IntoElement {
    let (label, color) = match kind {
        ObjectKind::Cell => ("cell", theme::accent()),
        ObjectKind::Receipt => ("receipt", theme::good()),
        ObjectKind::Capability => ("capability", theme::accent()),
        ObjectKind::Image => ("image", theme::warn()),
        ObjectKind::Proof => ("proof", theme::good()),
        ObjectKind::Factory => ("factory", theme::accent()),
        ObjectKind::Nullifier => ("nullifier", theme::warn()),
    };
    div().mb_2().child(pill(label, color))
}

/// A short label + color for a cell's lifecycle state (the OBJECTS panel's
/// lifecycle column). Matches the protocol's `CellLifecycle` variants.
fn lifecycle_badge(lc: &dregg_cell::lifecycle::CellLifecycle) -> (&'static str, Hsla) {
    use dregg_cell::lifecycle::CellLifecycle;
    match lc {
        CellLifecycle::Live => ("live", theme::good()),
        CellLifecycle::Sealed { .. } => ("sealed", theme::warn()),
        CellLifecycle::Destroyed { .. } => ("destroyed", theme::bad()),
        CellLifecycle::Migrated { .. } => ("migrated", theme::muted()),
        CellLifecycle::Archived { .. } => ("archived", theme::accent()),
    }
}

/// A compact row for a reflected object (the cipherclerk panel's identity /
/// token / delegation entries), showing its title, kind badge, and fields.
fn inspectable_row(ins: &Inspectable) -> impl IntoElement {
    let mut col = div()
        .flex()
        .flex_col()
        .gap_0p5()
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel())
        .child(
            div()
                .flex()
                .justify_between()
                .child(div().text_xs().text_color(theme::text()).child(ins.title.clone()))
                .child(kind_badge(ins.kind)),
        )
        .child(div().text_xs().text_color(theme::muted()).child(ins.subtitle.clone()));
    for f in &ins.fields {
        col = col.child(field_row(f));
    }
    col
}

fn field_row(f: &Field) -> impl IntoElement {
    let (val, color): (String, Hsla) = match &f.value {
        FieldValue::Text(s) => (s.clone(), theme::text()),
        FieldValue::Balance(b) => (
            b.to_string(),
            if *b < 0 { theme::warn() } else { theme::text() },
        ),
        FieldValue::Count(c) => (c.to_string(), theme::text()),
        FieldValue::Bool(b) => (
            b.to_string(),
            if *b { theme::good() } else { theme::muted() },
        ),
        FieldValue::Id(id) => (reflect::short_hex(id), theme::accent()),
        FieldValue::Hash(h) => (reflect::short_hex(h), theme::good()),
        FieldValue::CapEdge { target, slot } => {
            (format!("→ {} (slot {slot})", reflect::short_hex(target)), theme::accent())
        }
        FieldValue::FieldSlot { hex, .. } => (reflect::short_hex_hexstr(hex), theme::muted()),
    };
    div()
        .flex()
        .justify_between()
        .py_0p5()
        .child(div().text_xs().text_color(theme::muted()).child(f.key.clone()))
        .child(div().text_xs().text_color(color).child(val))
}

/// A verb button that runs a `&mut Cockpit` method through the listener.
fn verb_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    let id = SharedString::from(format!("verb-{label}"));
    div()
        .id(id)
        .px_3()
        .py_2()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_color(color)
        .cursor_pointer()
        .hover(|s| s.bg(theme::border()))
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev, _window, cx| {
                handler(this, cx);
            }),
        )
        .child(label.to_string())
}

/// A compact cipherclerk action button (smaller than a composer verb; the
/// clerk panel has four in a wrap row).
fn clerk_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    let id = SharedString::from(format!("clerk-{label}"));
    div()
        .id(id)
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_xs()
        .text_color(color)
        .cursor_pointer()
        .hover(|s| s.bg(theme::border()))
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev, _window, cx| {
                handler(this, cx);
            }),
        )
        .child(label.to_string())
}

/// A short label + color for a palette command's category badge.
fn category_badge(cat: Category) -> (&'static str, Hsla) {
    match cat {
        Category::Verb => (cat.label(), theme::good()),
        Category::Navigate => (cat.label(), theme::accent()),
        Category::Replay => (cat.label(), theme::warn()),
        Category::Clerk => (cat.label(), theme::accent()),
        Category::Shell => (cat.label(), theme::accent()),
        Category::Ide => (cat.label(), theme::good()),
        Category::Debug => (cat.label(), theme::warn()),
        Category::Inspect => (cat.label(), theme::muted()),
        Category::Palette => (cat.label(), theme::muted()),
    }
}

/// A short label + color for a surface's SHELL-DRAWN trusted-path lifecycle
/// badge (the anti-spoof identity chrome). Mirrors the shell's lifecycle strings.
fn identity_badge(lifecycle: &str) -> (&'static str, Hsla) {
    match lifecycle {
        "live" => ("live", theme::good()),
        "sealed" => ("sealed", theme::warn()),
        "destroyed" => ("destroyed", theme::bad()),
        "migrated" => ("migrated", theme::muted()),
        "archived" => ("archived", theme::accent()),
        "system" => ("system", theme::warn()),
        _ => ("missing", theme::bad()),
    }
}

/// A compact shell-toolbar button (the cap-first compositor's window ops). Same
/// shape as a clerk button; runs a `&mut Cockpit` method through the listener.
fn shell_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    let id = SharedString::from(format!("shell-{label}"));
    div()
        .id(id)
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_xs()
        .text_color(color)
        .cursor_pointer()
        .hover(|s| s.bg(theme::border()))
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev, _window, cx| {
                handler(this, cx);
            }),
        )
        .child(label.to_string())
}
