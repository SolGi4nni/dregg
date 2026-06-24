//! Construction (`with_node`) + select-by-name + the per-frame state maintenance (refresh/fold/invalidate) + demo seeding.

use super::*;

impl Cockpit {
    /// Select the active tab by (case-insensitive) name — matched against each
    /// [`Tab::label`] with separators/symbols stripped (so `"inspector"`,
    /// `"inspect-act"`, `"web-of-cells"`, `"proofs"` all resolve). Used by the
    /// headless bake to screenshot a specific surface. Returns whether a tab
    /// matched (the active tab is left unchanged on a miss).
    pub fn select_tab_named(&mut self, name: &str) -> bool {
        let norm = |s: &str| {
            s.chars()
                .filter(|c| c.is_ascii_alphanumeric())
                .flat_map(|c| c.to_lowercase())
                .collect::<String>()
        };
        let want = norm(name);
        // The ⌘K palette is an overlay, not a Tab — but the headless bake reaches
        // surfaces by name (`--render-tab`), so honor "palette" by opening it. This
        // lets the bake capture the palette (and its now-scrollable result list).
        if want == "palette" {
            self.palette.open();
            return true;
        }
        for &t in Tab::ALL.iter() {
            if norm(t.label()) == want {
                self.tab = t;
                return true;
            }
        }
        false
    }

    /// Construct the cockpit, optionally connecting to a LIVE remote node at
    /// `node_url` (the master interface ALSO watching a running federation). When
    /// present, the SSE receipt stream is opened immediately so the live receipt
    /// list begins filling (each streamed receipt fires `cx.notify()` on render).
    pub fn with_node(
        world: Rc<RefCell<World>>,
        anchors: [CellId; 3],
        focus: FocusHandle,
        node_url: Option<String>,
        pending_seed: Option<world::DemoSeed>,
    ) -> Self {
        let cells = sorted_cells(&world.borrow());

        // Seed the debugger with a demo turn (treasury → user transfer) that
        // the operator can step + explain against the live world.
        let [treasury, service, user] = anchors;
        let debug_turn = world
            .borrow()
            .turn(treasury, vec![world::transfer(treasury, user, 1_000)]);

        // Seed the cipherclerk vault with two real HD-derived identities.
        let mut clerk = cipherclerk::Cipherclerk::new();
        clerk.add_identity(cipherclerk::Identity::from_byte(
            "alice",
            "dregg/cockpit",
            0x01,
        ));
        clerk.add_identity(cipherclerk::Identity::from_byte(
            "bob",
            "dregg/cockpit",
            0x02,
        ));

        // Seed the editor with a conserving demo forest already validated.
        let mut editor = edit::EditorState::default();
        editor.set_artifact("Transfer 250 treasury→user (1 root, conserving)");
        {
            let mut fb = edit::ForestBuilder::new();
            fb.root(edit::ActionBuilder::new(treasury).effect(
                dregg_turn::action::Effect::Transfer {
                    from: treasury,
                    to: user,
                    amount: 250,
                },
            ));
            editor.set_verdict(edit::validate(fb.forest()));
        }

        // Start the replay scrubber at the head of the live world's history.
        let replay_cursor = world.borrow().recorded_turns().len();
        // The ⏳ TIME tab's scrubber also starts at the live present (the head).
        let time_cursor = replay_cursor;

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

        // M3 — THE INSPECTOR'S OWN VIEW CELL (the reflexive migration §3): the
        // moldable inspector's camera-aim (focus + present-idx) is self-hosted as a
        // REAL cell (the BufferCell two-tier split, generalized). A fresh dedicated
        // cell backs it; the draft is aimed at the treasury and committed once so the
        // witnessed (prior-frame) aim is populated. A re-focus mutates the free draft
        // and lands an occasional witnessed SetField commit (the §3.5 stream weight
        // class). The inspector is now itself inspectable (FocusTarget::ViewCell).
        let inspector_view_backing = world.borrow_mut().genesis_cell(0x5E, 0);
        let inspector_view = {
            let v = starbridge_v2::view_cell::ViewCell::focused(
                inspector_view_backing,
                "INSPECTOR",
                treasury,
            );
            // Land the initial aim so the witnessed state matches the boot draft.
            let _ = v.commit(&mut world.borrow_mut());
            v
        };

        // M3 WIDEN — THE WORKSPACE CELL (the §3.4 selector move): the cockpit's
        // active-tab selector is self-hosted as a REAL cell (the same two-tier split
        // as the inspector's view cell). A fresh dedicated cell backs it; the draft is
        // seeded to the boot tab (`Home` = index 0) and committed once so the witnessed
        // (prior-frame) selector is populated. A tab switch mutates the free draft
        // (`self.tab`) and lands an occasional witnessed `SetField` commit — the active
        // tab becomes a rewindable dregg-graph mutation, conserving nothing.
        let workspace_cell_backing = world.borrow_mut().genesis_cell(0x5F, 0);
        let workspace_cell = {
            // RESTORE from the (possibly recovered) durable image first: a reopened
            // image already carries the witnessed active-tab AND the torn-off-tabs
            // bitset on this backing cell, replayed by recovery. `from_world` rebuilds
            // the free draft from that committed state. On a fresh image the cell was
            // just genesis-installed with no `SetField` turns, so the restore reads the
            // boot defaults `(tab=0, torn=0)`.
            let restored = starbridge_v2::view_cell::WorkspaceCell::from_world(
                &world.borrow(),
                workspace_cell_backing,
            );
            // Witness the boot default ONLY when the cell was never committed (a fresh
            // image — nonce 0), so a relaunch does NOT clobber the restored tab/pop-out
            // state with `(Home, nothing torn)`.
            if restored.revision(&world.borrow()) == 0 {
                let boot = starbridge_v2::view_cell::WorkspaceCell::new(
                    workspace_cell_backing,
                    Tab::Home.index(),
                );
                let _ = boot.commit(&mut world.borrow_mut());
                boot
            } else {
                restored
            }
        };

        // The POWERBOX (CapDesk) demo: birth a fresh CONFINED app-cell that holds
        // NO ambient authority (a freshly-launched app-as-cell), and seed the user
        // principal (the cockpit's own identity, `user`) with a held cap reaching
        // the `service` cell — so the powerbox picker is non-empty (the user has
        // SOMETHING to designate) and a grant demonstrates real attenuation away
        // from the held authority. The user genuinely holds this cap; the powerbox
        // can only ever offer the user's own authority (`mint_needs_held_factory`).
        let powerbox_app = world.borrow_mut().genesis_cell(0xA9, 0);
        // The user holds full (None) authority reaching `service` — the powerbox can
        // confer this or any narrower right, never wider. The grant rides an ORDERED
        // turn: `service` SELF-GRANTS the cap to `user` (the cap target IS the
        // service cell, so the executor's self-grant arm authorizes it by service's
        // own consent — service is an open anchor cell). The anchors are already
        // turn-touched by the seed turns, so a genesis-path grant here would be a
        // MID-SESSION genesis mutation (the persist-durability category error); the
        // turn lands a `CommitRecord` so a durable cockpit image reproduces it.
        {
            let mut w = world.borrow_mut();
            let t = w.turn(
                service,
                vec![world::grant_capability(service, user, service, 0)],
            );
            let _ = w.commit_turn(t);
        }
        // …and reaching `treasury` too (same self-grant shape), so the WEB-OF-CELLS ⚡
        // "make interactive" upgrade (a real powerbox grant over the transcluded
        // SOURCE) lands on a cell the user genuinely holds whatever the transclusion
        // picks as its source among the principal cells (the powerbox still REFUSES
        // any source the user does not hold — `mint_needs_held_factory`).
        {
            let mut w = world.borrow_mut();
            let t = w.turn(
                treasury,
                vec![world::grant_capability(treasury, user, treasury, 0)],
            );
            let _ = w.commit_turn(t);
        }

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
                    (
                        treasury,
                        "worker-b (unreachable — the confinement boundary)",
                    ),
                ],
            )
        };

        // The LIVE NODE connection (`--node <url>`): wrap an HTTP client, open the
        // SSE receipt stream right away (the reader runs on its own thread and feeds
        // the pure parser; the cockpit drains the channel under `cx.notify()`), and
        // take one blocking snapshot for the initial reflections. All best-effort:
        // an unreachable node leaves the embedded image fully usable.
        let (live_node, live_stream, live_snapshot) = match node_url {
            Some(url) => {
                let ln = starbridge_v2::client::LiveNode::new(
                    starbridge_v2::client::NodeClient::http(url),
                );
                let stream = ln.connect_stream();
                let snapshot = ln.sync().ok();
                (Some(ln), stream, snapshot)
            }
            None => (None, None, None),
        };
        let live_feed = starbridge_v2::live_node::ReceiptFeed::new(256);

        // The attenuation dial's ceiling: the FIRST cap the `user` principal genuinely
        // holds (the constructor granted user→service + user→treasury via the real
        // genesis grant path). Computed here, before `world` is moved into the struct.
        let lane_dial = HeldCapability::all_for(&world.borrow(), user)
            .first()
            .map(AttenuationDial::over_held);

        // Seed the dynamics cursor at the live head so the first render does not
        // re-fold the genesis events whose cells `self.cells` already carries.
        let dynamics_cursor = world.borrow().dynamics().cursor();

        Self {
            world,
            cells,
            dynamics_cursor,
            present_memo: PresentMemo::new(),
            selection: Selection::Image,
            last_outcome: None,
            anchors,
            // BOOT into the warm landing PORTAL — the alive front door of the
            // live verified image (text-rich, self-describing). SHELL and the
            // other rooms are one click (or ⌘K) away.
            tab: Tab::Home,
            // BOOT into INHABIT — Home is its primary surface (the active mode is
            // DERIVED from the active surface via `Tab::mode`). The dev dock starts
            // collapsed (⌘J reveals it).
            dock_open: false,
            workspace_cell,
            tab_witness_pending: false,
            debug_turn,
            breakpoints: vec![debug::Breakpoint::OnRefusal, debug::Breakpoint::OnConservationBreak],
            replay_cursor,
            replay_fork: None,
            time_cursor,
            meta_stack: MetaStack::new(),
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
            // LAZY: the metered demo world + factory deploy + the slow proof-bearing
            // demo turns must NOT sit on the first-paint path. Booted on first SWARM
            // navigation / killer-demo verb (see `killer_demo()` + `set_tab`).
            killer_demo: None,
            killer_demo_lines: Vec::new(),
            pending_seed,
            palette: CommandPalette::new(),
            palette_scroll: UniformListScrollHandle::new(),
            focus,
            live_node,
            live_stream,
            live_feed,
            live_snapshot,
            web_cells_opened: None,
            web_cells_viewer_rights: dregg_cell::AuthRequired::Either,
            web_cells_outcome: None,
            web_cells_upgraded: None,
            web_cells_transclusion_outcome: None,
            // WHAT-LINKS-HERE: focus the cockpit's own `user` principal at depth 2
            // (direct backlinks + one hop of backlinks-of-backlinks) so the panel
            // boots into a populated docuverse map rather than an empty pane. Boot as
            // ROOT (None) so the gated backlinks are visible; the toggle drops to
            // Signature to watch them fog.
            links_here_focus: None,
            links_here_depth: 2,
            links_here_viewer_rights: dregg_cell::AuthRequired::None,
            // THE DOCS EDITOR boots on a real document cell with a single seeded
            // sentence (a real cap-gated turn), so the panel opens on live content.
            doc_editor: starbridge_v2::doc_editor::DocEditor::new(),
            doc_outcome: None,
            powerbox_app: Some(powerbox_app),
            // Default to the narrow Signature tier so a click demonstrates real
            // attenuation away from the user's wider (None) held authority.
            powerbox_confer_rights: dregg_cell::AuthRequired::Signature,
            powerbox_outcome: None,
            // The boot-seeded demo app (above) is the FIRST entry — the launcher
            // appends a fresh confined app per "+ launch" press.
            launched_apps: Vec::new(),
            // The SIMULATE composer boots with the treasury as agent, the target
            // picker on the first cell, the effect picker on the first palette
            // entry, and a seeded example action (a small treasury→user transfer)
            // so the panel opens on a runnable what-if rather than an empty forest.
            sim_draft: {
                let [treasury, _service, user] = anchors;
                let mut d = starbridge_v2::simulate::IntentDraft::new(treasury);
                let ai = d.add_action(treasury);
                d.add_effect(
                    ai,
                    starbridge_v2::simulate::EffectKind::Transfer { to: user, amount: 250 },
                );
                d
            },
            sim_target_idx: 0,
            sim_effect_idx: 0,
            sim_outcome: None,
            sim_commit_banner: None,

            // THE MOLDABLE INSPECTOR boots focused on the treasury (a populated
            // presentation set: RawFields + Affordances + Provenance + Graph +
            // Lifecycle), on its first sub-tab, with an empty spotter box. The
            // focus/present-idx now ride `inspector_view` (the M3 view cell).
            inspector_view,
            inspector_reflexive: false,
            nav_hist: Vec::new(),
            nav_cursor: 0,
            nav_jumping: false,
            nav_pins: Vec::new(),
            macro_recording: None,
            last_macro: None,
            macro_outcome: None,
            moldable_query: String::new(),
            moldable_lens: MoldableLens::Cell,

            // THE INSPECT→ACT loop boots on the treasury too.
            inspect_act_focus: Some(treasury),
            inspect_act_outcome: None,

            // THE WORKSPACE boots with a seeded conserving transfer draft so the
            // panel opens on a runnable doIt rather than an empty expression.
            workspace: {
                let mut ws = Workspace::new(treasury);
                ws.draft_mut().add_action(treasury);
                let ai = 0;
                ws.draft_mut().add_effect(
                    ai,
                    starbridge_v2::simulate::EffectKind::Transfer { to: user, amount: 250 },
                );
                ws
            },
            workspace_target_idx: 0,

            // THE LANES boot on the predicate composer, with a real non-vacuous
            // composite (a solvency floor), a turn-builder seeded with a conserving
            // transfer, the attenuation dial over a cap the user genuinely holds (the
            // constructor granted user→service + user→treasury), and a macaroon loop.
            lane_idx: 0,
            lane_composite: Composite::Leaf(Atom::BalanceGte { min: 100 }),
            lane_turn: {
                let mut g = CommittingTurnGadget::new(treasury);
                g.action_with(
                    user,
                    starbridge_v2::simulate::EffectKind::Transfer { to: user, amount: 250 },
                );
                g
            },
            lane_dial,
            lane_token: TokenLoopGadget::new([0x5Au8; 64], "dregg/service", [0x11u8; 32]),
            lane_outcome: None,
            // The ⤳ SHARE surface starts empty — the operator captures the focused
            // view to open the editor. The preview defaults to the WIDE recipient.
            share_editor: None,
            share_artifacts: Vec::new(),
            share_preview_wide: true,
            share_outcome: None,
            // LAZY: the pane group needs `window`/`cx`/`cx.entity()`, seeded on the
            // first render (`ensure_pane_group`).
            pane_group: None,
            active_pane: None,
            // SURFACE MIGRATION: no surfaces torn off at boot (the single-window
            // cockpit). The registry fills as the operator pops panes out.
            window_registry: WindowRegistry::new(),
            torn_restored: false,
            // THE ⚙ DEVTOOLS surface boots on the NETWORK sub-tab with an empty
            // filter (the whole data plane in view).
            devtools_sub: 0,
            devtools_filter: String::new(),
            // THE WEB-SHELL BROWSER — the URL-bar input entity is seeded lazily on
            // the first render (`ensure_webshell_input` needs a live `&mut Window`).
            // It boots on a sensible default page so the tile renders immediately.
            webshell_input: None,
            webshell_history: vec!["https://example.com".to_string()],
            webshell_cursor: 0,
            webshell_status: "press ↵ Go to render the page (real Servo WebView → SWGL → glass, behind the net-cap gate)".to_string(),
            #[cfg(feature = "servo")]
            webshell_frame: None,
            webshell_input_pending: None,
            // The live inspector card mounts lazily on the first Inspect-surface paint
            // (`ensure_inspector_card` builds it from the focused cell over the World).
            #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
            inspector_card: None,
        }
    }

    pub(crate) fn refresh_cells(&mut self) {
        self.cells = sorted_cells(&self.world.borrow());
    }

    /// M2 — THE DELTA FOLD. Pull every dynamics event since the last render and
    /// route each into per-slice invalidation (the dirty-set), then advance the
    /// cursor to the live head. This is the producer↔consumer join: the touched
    /// cell, alone, re-lights its projection (`EFFICIENCY-WELD-PLAN.md` §2.1).
    pub(crate) fn fold_dynamics(&mut self) {
        let new = {
            let w = self.world.borrow();
            let from = self.dynamics_cursor;
            // Clone the slice out so we drop the world borrow before mutating self.
            let slice = w.dynamics().since(from).to_vec();
            self.dynamics_cursor = w.dynamics().cursor();
            slice
        };
        for ev in &new {
            self.invalidate_for(ev);
        }
    }

    /// The §2.2 variant→invalidation table: what each `WorldEvent` dirties.
    pub(crate) fn invalidate_for(&mut self, ev: &dynamics::WorldEvent) {
        use dynamics::WorldEvent as E;
        match ev {
            // A cell was born. ZERO is the `CreateCell`/`FromFactory` sentinel (the
            // real id isn't known at emit): we don't know which cell appeared, so
            // refresh `self.cells` from the ledger (the bounded full-rescan case,
            // once per cell-creating turn) and drop the whole projection cache.
            E::CellBorn { cell, .. } => {
                if *cell == CellId::ZERO {
                    self.refresh_cells();
                    self.present_memo.invalidate_all();
                } else {
                    // A real-id birth (genesis seed): keep cells sorted-correct and
                    // drop any (now-resolvable) cached projection for it.
                    if !self.cells.contains(cell) {
                        self.cells.push(*cell);
                        self.cells.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
                    }
                    self.present_memo.invalidate_cell(*cell);
                }
            }
            E::CellDestroyed { cell } => {
                self.cells.retain(|c| c != cell);
                self.present_memo.invalidate_cell(*cell);
            }
            E::BalanceFlowed { cell, .. }
            | E::FieldSet { cell, .. }
            | E::CellMutated { cell }
            | E::CellSealed { cell }
            | E::CellUnsealed { cell }
            | E::Burned { cell, .. }
            | E::EventEmitted { cell, .. } => {
                self.present_memo.invalidate_cell(*cell);
            }
            E::SurfaceDamaged { cell, owner, .. } => {
                self.present_memo.invalidate_cell(*cell);
                self.present_memo.invalidate_cell(*owner);
            }
            // Cap-edge deltas reach OTHER cells' affordance badges (viewer-non-
            // local, §4.2): conservatively drop the whole affordance cache.
            E::CapabilityGranted { from, to } => {
                self.present_memo.invalidate_cell(*from);
                self.present_memo.invalidate_cell(*to);
                self.present_memo.invalidate_affordances_all();
            }
            E::CapabilityRevoked { cell, .. } => {
                self.present_memo.invalidate_cell(*cell);
                self.present_memo.invalidate_affordances_all();
            }
            // A height tick carries no cell-specific invalidation of its own; the
            // per-cell events in the SAME commit batch carry the actual deltas, and
            // `rail_header` re-reads the root via the M1 memo (height bumped).
            E::TurnCommitted { .. } => {}
            // Nothing moved — only the outcome banner (already a Rust field).
            E::TurnRejected { .. } => {}
            // A turn was STAGED while the world is suspended (the meta-debug
            // Suspend gate). The head is frozen — nothing in the ledger moved —
            // but the staged continuation grew, which a `DebugFrame` view reads
            // off the world directly. Drop any cached meta-frame projection so a
            // re-present picks up the new pending count.
            E::TurnQueued { .. } => {}
        }
    }

    /// Whether there are demo seed turns still waiting to be committed (drives the
    /// post-paint async seeding loop in `main::run_window`).
    pub fn has_pending_seed(&self) -> bool {
        self.pending_seed.as_ref().is_some_and(|s| !s.is_done())
    }

    /// **Commit the NEXT demo seed turn** against the live world (the real executor),
    /// refresh the cell rail + the live banner, and `cx.notify()` so the new cell/
    /// receipt paints immediately. Returns `true` if MORE seed turns remain (the
    /// caller loops, yielding between calls so the UI breathes), `false` once the
    /// image is fully seeded.
    ///
    /// This is the paint-friendly counterpart to `demo_world`'s eager seeding: the
    /// SAME five verified turns, run one-per-yield AFTER the window is already up,
    /// so the cockpit was alive instantly and the demo provenance fills in live.
    pub fn seed_next_demo_turn(&mut self, cx: &mut Context<Self>) -> bool {
        let Some(seed) = self.pending_seed.as_mut() else {
            return false;
        };
        // Commit exactly one real turn against the shared world.
        let label = {
            let mut w = self.world.borrow_mut();
            seed.next(&mut w)
        };
        let more = !self.pending_seed.as_ref().unwrap().is_done();
        if let Some(label) = label {
            // A live status line so the operator SEES the image populating.
            let remaining = self.pending_seed.as_ref().unwrap().remaining();
            self.last_outcome = Some(if more {
                format!("seeding the live image — {label} ({remaining} more)")
            } else {
                format!("seeding the live image — {label} (demo image ready)")
            });
            self.refresh_cells();
        }
        if !more {
            // Fully seeded — drop the plan.
            self.pending_seed = None;
        }
        cx.notify();
        more
    }

    // --- the verbs (each runs the REAL embedded executor) -------------------
}
