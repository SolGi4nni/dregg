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
use starbridge_v2::world::{self, CommitOutcome, World};
// The feature panels — wired in as tabs of the master interface.
use starbridge_v2::{cipherclerk, debug, edit, replay};

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
    Composer,
    Objects,
    Debugger,
    Replay,
    Cipherclerk,
    Editor,
}

impl Tab {
    const ALL: [Tab; 6] = [
        Tab::Composer,
        Tab::Objects,
        Tab::Debugger,
        Tab::Replay,
        Tab::Cipherclerk,
        Tab::Editor,
    ];
    fn label(self) -> &'static str {
        match self {
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
        let [treasury, _service, user] = anchors;
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

        Self {
            world,
            cells,
            selection: Selection::Image,
            last_outcome: None,
            anchors,
            tab: Tab::Composer,
            debug_turn,
            breakpoints: vec![debug::Breakpoint::OnRefusal, debug::Breakpoint::OnConservationBreak],
            replay_cursor,
            replay_fork: None,
            clerk,
            clerk_outcome: None,
            editor,
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
            Some(s) if s.contains("REJECTED") => (s.clone(), theme::bad()),
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
            Tab::Composer => self.composer(cx).into_any_element(),
            Tab::Objects => self.objects_panel().into_any_element(),
            Tab::Debugger => self.debugger_panel().into_any_element(),
            Tab::Replay => self.replay_panel().into_any_element(),
            Tab::Cipherclerk => self.cipherclerk_panel(cx).into_any_element(),
            Tab::Editor => self.editor_panel().into_any_element(),
        }
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
        Category::Debug => (cat.label(), theme::warn()),
        Category::Inspect => (cat.label(), theme::muted()),
        Category::Palette => (cat.label(), theme::muted()),
    }
}
