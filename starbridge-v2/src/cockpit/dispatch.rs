//! Command dispatch (the ⌘K palette↔button single path), tab selection/witnessing, key handling, outcome notes.

use super::*;

impl Cockpit {
    // --- THE CENTRAL DISPATCHER — one path for buttons AND the palette -------

    /// Run a palette [`CommandId`] through the SAME `&mut Cockpit` verbs the
    /// buttons call. This is what keeps the ⌘K palette honestly "over ALL
    /// actions": there is no parallel action path — every command lands here and
    /// routes to the one method that already implements it.
    pub(crate) fn dispatch(&mut self, id: CommandId, cx: &mut Context<Self>) {
        match id {
            CommandId::Transfer => self.run_demo_transfer(cx),
            CommandId::ComposeMulti => self.run_compose_multi(cx),
            CommandId::Grant => self.run_demo_grant(cx),
            CommandId::CreateCell => self.run_demo_create(cx),
            CommandId::Seal => self.run_seal(cx),
            CommandId::Burn => self.run_burn(cx),
            CommandId::OverGrant => self.run_over_grant(cx),

            // The WHAT-IF / SIMULATE composer (navigate to the tab on a verb so
            // the prediction is in view).
            CommandId::SimRun => {
                self.set_tab(Tab::Simulate, cx);
                self.sim_run(cx);
            }
            CommandId::SimCommit => {
                self.set_tab(Tab::Simulate, cx);
                self.sim_commit(cx);
            }
            CommandId::SimAddEffect => {
                self.set_tab(Tab::Simulate, cx);
                self.sim_add_effect(cx);
            }

            CommandId::GoComposer => self.set_tab(Tab::Composer, cx),
            CommandId::GoSimulate => self.set_tab(Tab::Simulate, cx),
            CommandId::GoObjects => self.set_tab(Tab::Objects, cx),
            CommandId::GoDebugger => self.set_tab(Tab::Debugger, cx),
            CommandId::GoReplay => self.set_tab(Tab::Replay, cx),
            CommandId::GoCipherclerk => self.set_tab(Tab::Cipherclerk, cx),
            CommandId::GoEditor => self.set_tab(Tab::Editor, cx),
            CommandId::GoHome => self.set_tab(Tab::Home, cx),
            CommandId::GoShell => self.set_tab(Tab::Shell, cx),
            CommandId::GoAgent => self.set_tab(Tab::Agent, cx),
            CommandId::GoBuffer => self.set_tab(Tab::Buffer, cx),
            CommandId::GoTerminal => self.set_tab(Tab::Terminal, cx),
            CommandId::GoSwarm => self.set_tab(Tab::Swarm, cx),
            CommandId::GoGraph => self.set_tab(Tab::Graph, cx),
            CommandId::GoOrgans => self.set_tab(Tab::Organs, cx),
            CommandId::GoProofs => self.set_tab(Tab::Proofs, cx),
            CommandId::GoPowerbox => self.set_tab(Tab::Powerbox, cx),
            CommandId::LaunchConfinedApp => self.run_launch_confined_app(cx),

            CommandId::BufferType => self.buffer_type_demo(cx),
            CommandId::BufferCommit => self.buffer_commit(cx),
            CommandId::BufferReadOnlyWrite => self.buffer_readonly_write_demo(cx),
            CommandId::TerminalRunInMandate => self.terminal_run_in_mandate(cx),
            CommandId::TerminalRunOutOfMandate => self.terminal_run_out_of_mandate(cx),

            // The self-hosting dev panes. Opening one needs a live `&mut Window`
            // (a fresh surface mounts into the pane group), but `dispatch` runs
            // from the key/palette handler with only a `Context`. So defer the
            // open to re-enter the cockpit's window AFTER the current update
            // unwinds (the window box is back in its slot) — then build + graft
            // the pane with the window in hand. When `dev-surfaces` is off these
            // are commands without a body (the palette stays comprehensive).
            #[cfg(feature = "dev-surfaces")]
            CommandId::OpenTerminalPane => {
                self.open_dev_pane_deferred(cx, Cockpit::open_terminal_pane)
            }
            #[cfg(feature = "dev-surfaces")]
            CommandId::OpenEditorPane => {
                self.open_dev_pane_deferred(cx, Cockpit::open_editor_pane)
            }
            #[cfg(not(feature = "dev-surfaces"))]
            CommandId::OpenTerminalPane | CommandId::OpenEditorPane => {}

            CommandId::SwarmCoordinatorEmitA => self.swarm_coordinator_emit_a(cx),
            CommandId::SwarmWorkerADrain => self.swarm_worker_a_drain(cx),
            CommandId::SwarmCoordinatorTransferAndWake => {
                self.swarm_coordinator_transfer_and_wake(cx)
            }

            CommandId::KillerDemoAdvance => self.killer_demo_advance(cx),
            CommandId::KillerDemoRunAll => self.killer_demo_run_all(cx),
            CommandId::KillerDemoOverShare => self.killer_demo_over_share(cx),
            CommandId::KillerDemoReset => self.killer_demo_reset(cx),

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

    pub(crate) fn set_tab(&mut self, tab: Tab, cx: &mut Context<Self>) {
        // Navigating to SWARM is where the killer demo lives — boot it lazily HERE
        // (on the click), so the metered-world + factory-deploy cost lands on the
        // navigation rather than on the first paint. The SWARM panel then always
        // has a booted demo to reflect. (Every other tab leaves it `None`.)
        if matches!(tab, Tab::Swarm) {
            let _ = self.killer_demo();
        }
        // OPTIMISTIC NAV — move the free draft + repaint AT ONCE. `active_tab()`
        // prefers the draft while a witness is pending, so the panel switches on this
        // very frame; the witnessed `SetField` commit (the slow part — a real executor
        // turn) is deferred OFF the paint path below.
        self.tab = tab;
        cx.notify();
        self.schedule_witness_tab(cx);
    }

    /// OPTIMISTIC NAV — queue the witnessed-tab commit on the foreground async
    /// executor (gpui is `!Send`; this is a foreground [`Context::spawn`] task, not a
    /// thread — the `&mut self` witness work runs back on the main loop via the weak
    /// entity, just deferred past the current paint). Coalesces: a burst of rapid
    /// tab-flips queues ONE task (guarded by `tab_witness_pending`), which commits the
    /// LATEST `self.tab` once — so neither the click nor the witnessed UI-history
    /// balloons. A no-op (other than the eventual commit) when one is already queued.
    pub(crate) fn schedule_witness_tab(&mut self, cx: &mut Context<Self>) {
        if self.tab_witness_pending {
            return;
        }
        // Cheap no-op guard: the witnessed selector already matches the draft, so
        // there is nothing to commit — don't queue a task (and don't churn the
        // ledger) every frame. `None` (cell never witnessed) still schedules once.
        if self.workspace_cell.committed_tab(&self.world.borrow()) == Some(self.tab.index()) {
            return;
        }
        self.tab_witness_pending = true;
        cx.spawn(async move |this, cx| {
            // A short beat: let the optimistic repaint land first, and let a burst of
            // flips collapse so we witness only the settled tab.
            cx.background_executor()
                .timer(std::time::Duration::from_millis(16))
                .await;
            // Re-enter the entity on the foreground loop and land the (latest) commit.
            let _ = this.update(cx, |this, _cx| {
                this.tab_witness_pending = false;
                this.witness_tab();
            });
        })
        .detach();
    }

    /// M3 WIDEN — THE WITNESSED ACTIVE TAB (`render(workspace_subgraph)`, §3.4). The
    /// tab `render()` dispatches on. While a witness commit is pending (OPTIMISTIC
    /// NAV), the FREE DRAFT (`self.tab`) is the visible aim — so a click repaints at
    /// once. Otherwise it reads the [`WorkspaceCell`]'s committed (witnessed) selector
    /// index — the whole cockpit selector is cell-driven, not a Rust field. A dangling
    /// cell (gone from the ledger) degrades to the live draft.
    pub(crate) fn active_tab(&self) -> Tab {
        // The optimistic aim wins until the deferred commit catches the cell up.
        if self.tab_witness_pending {
            return self.tab;
        }
        match self.workspace_cell.committed_tab(&self.world.borrow()) {
            Some(idx) => Tab::from_index(idx),
            // The backing cell is absent (never in the boot path) — fall to the free
            // draft so the cockpit is never blank.
            None => self.tab,
        }
    }

    /// M3 WIDEN — sync the workspace cell's free draft to the live `self.tab` and land
    /// an occasional witnessed `SetField` commit (the [`BufferCell`] commit discipline,
    /// generalized to the tab selector). A no-op when already clean. A commit failure
    /// leaves the free draft moved (the panel still reflects the operator's aim); the
    /// witnessed selector catches up on the next successful witness. The active tab is
    /// therefore a real, rewindable cell mutation, conserving nothing (§3.5).
    pub(crate) fn witness_tab(&mut self) {
        self.workspace_cell.set_active_tab(self.tab.index());
        if !self.workspace_cell.is_clean(&self.world.borrow()) {
            let _ = self.workspace_cell.commit(&mut self.world.borrow_mut());
        }
    }

    /// Focus the cockpit root so it receives key events (called on window open).
    pub fn focus_on_open(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        window.focus(&self.focus, cx);
    }

    // --- the ⌘K key handler -------------------------------------------------

    /// Handle a key event. ⌘K toggles the palette; while it is open, typed
    /// characters filter, ↑/↓ move the selection, Enter dispatches, Esc closes.
    /// Returns nothing — it mutates palette state + may dispatch a command.
    pub(crate) fn on_key(&mut self, ev: &KeyDownEvent, cx: &mut Context<Self>) {
        let ks = &ev.keystroke;
        let key = ks.key.as_str();
        let cmd = ks.modifiers.platform || ks.modifiers.control;

        // ⌘K / Ctrl-K toggles the palette from anywhere.
        if cmd && key == "k" {
            self.palette.toggle();
            cx.notify();
            return;
        }

        // ⌘[ / ⌘] — browser-style navigation back/forward through the UI history.
        if cmd && key == "[" {
            self.nav_back(cx);
            return;
        }
        if cmd && key == "]" {
            self.nav_forward(cx);
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

    pub(crate) fn note_outcome(&mut self, outcome: CommitOutcome) {
        self.last_outcome = Some(match outcome {
            CommitOutcome::Committed { receipt, .. } => {
                // Jump the inspector to the new receipt.
                let idx = self.world.borrow().receipts().len().saturating_sub(1);
                self.selection = Selection::Receipt(idx);
                format!("committed · receipt {}", reflect::short_hex(&receipt.receipt_hash()))
            }
            CommitOutcome::Rejected { reason, .. } => format!("REJECTED by executor: {reason}"),
            // Suspended: the turn was staged in the pending queue, not run. The
            // live loop is halted (meta-debug Suspend gate); it commits on resume.
            CommitOutcome::Queued { agent } => {
                format!("queued · world suspended · {}", world::short(&agent))
            }
        });
    }

    // --- panels --------------------------------------------------------------

}
