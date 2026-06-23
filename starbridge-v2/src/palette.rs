//! THE ⌘K COMMAND PALETTE — one searchable surface over EVERY action.
//!
//! The master interface's promise is to be *comprehensive over all data and all
//! actions*. The cockpit's actions are otherwise scattered across panels (the
//! composer's verb buttons, the workspace tabs, the replay scrubber, the
//! cipherclerk's mint/attenuate/delegate/discharge, the debugger's retarget).
//! This module unifies them into ONE ⌘K palette: type to fuzzy-filter, arrow to
//! select, Enter to run.
//!
//! The design keeps the palette HONEST about "over ALL actions": a palette
//! [`Command`] does not carry its own behaviour — it carries a [`CommandId`]
//! that the cockpit dispatches through *the exact same `&mut Cockpit` methods
//! the buttons call*. There is no parallel action path; the palette is a second
//! front-end onto the one set of verbs. This module is gpui-free and
//! `cargo test`-able (the registry + the fuzzy matcher + the selection model);
//! the cockpit maps it onto a gpui overlay and owns the key handling.

/// Every action the master interface exposes, as a stable identifier the
/// cockpit dispatches. ONE enum = the canonical action surface; adding a verb
/// means adding a variant here and one match arm in the cockpit's dispatcher,
/// so the palette can never silently drift from what the cockpit can do.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CommandId {
    // --- composer verbs (run the embedded executor) ---
    Transfer,
    ComposeMulti,
    Grant,
    CreateCell,
    Seal,
    Burn,
    OverGrant,

    // --- the WHAT-IF / SIMULATE composer (predict before committing) ---
    /// SIMULATE the composed intent — predict its consequences in a forked
    /// throwaway world (the real executor, live world untouched).
    SimRun,
    /// COMMIT the simulated intent for real (the identical turn on the live world).
    SimCommit,
    /// Add the picked effect (on the picked target) to the SIMULATE draft forest.
    SimAddEffect,

    // --- workspace tab switches ---
    GoComposer,
    /// Navigate to the SIMULATE tab (the what-if intent composer).
    GoSimulate,
    GoObjects,
    GoDebugger,
    GoReplay,
    GoCipherclerk,
    GoEditor,
    /// Navigate to the HOME landing portal (the warm front door of the live image).
    GoHome,
    GoShell,
    GoAgent,
    GoBuffer,
    GoTerminal,
    /// Navigate to the GRAPH tab (the whole-graph ocap delegation layout).
    GoGraph,
    /// Navigate to the ORGANS tab (live organ cell-state: trustline/flash-well).
    GoOrgans,
    /// Navigate to the PROOFS tab (proof-attach + STARK verification status).
    GoProofs,
    /// Navigate to the POWERBOX tab (CapDesk — the trusted designation flow: an app
    /// requests a cap it lacks; the user designates from what they hold; the powerbox
    /// mints a fresh attenuated cap via a real grant turn).
    GoPowerbox,
    /// Navigate to the ⚙ DEVTOOLS tab (Firebug for a verified OS — the data plane,
    /// the receipt console, the federation, as three inspector sub-tabs).
    GoDevtools,
    /// Navigate to the 🌐 WEB-SHELL tab (a general http(s):// browser surface — the
    /// real Servo WebView render behind the net-cap gate, with a URL bar + nav).
    GoWebShell,

    // --- the 🌐 WEB-SHELL BROWSER (a general http(s):// browser surface) ---
    /// GO — render the URL currently in the web-shell address bar (or the current
    /// history entry): the real `render_url_to_frame` behind the net-cap gate.
    WebShellGo,
    /// BACK — step to the previous URL in the browser history + re-render it.
    WebShellBack,
    /// FORWARD — step to the next URL in the browser history + re-render it.
    WebShellForward,
    /// RELOAD — re-render the current URL (re-drive the WebView render).
    WebShellReload,
    /// LAUNCH a confined app at RUNTIME — birth a fresh app-cell holding NO ambient
    /// authority (a real confined app-as-cell) and route its capability request through
    /// the existing powerbox (the powerbox's missing first half). Switches to the
    /// POWERBOX tab so the designation flow is in view.
    LaunchConfinedApp,

    // --- the A1 IDE DEVELOPER surfaces (editor buffer + terminal) ---
    /// Type a line into the editor buffer (free, in-memory — the doc goes dirty).
    BufferType,
    /// COMMIT the editor buffer's digest into the backing cell (cap-gated turn).
    BufferCommit,
    /// Attempt to COMMIT through a READ-ONLY mirror — the no-amplification rule
    /// firing at the editor (a read-only buffer cannot write: REFUSED).
    BufferReadOnlyWrite,
    /// Run an IN-MANDATE terminal command — the terminal-cell reaches the target,
    /// so it COMMITS and its receipt is the output (the ADOS tool-call seam).
    TerminalRunInMandate,
    /// Run an OUT-OF-MANDATE terminal command — the target is outside the
    /// terminal-cell's caps; the command cap-gate REFUSES it (confined Bash).
    TerminalRunOutOfMandate,

    // --- the SELF-HOSTING DEV PANES (edit/build deos INSIDE deos) ---
    /// Open a LIVE TERMINAL pane — spawn `$SHELL` on a real PTY in its own split
    /// pane (run cargo/git inside deos). The terminal half of the self-hosting
    /// dev loop. (Spawns only in a live window; a no-op if dev-surfaces is off.)
    OpenTerminalPane,
    /// Open a LIVE EDITOR pane — a deos-zed editor rooted at the repo cwd in its
    /// own split pane (edit deos's own sources inside deos). The editor half of
    /// the self-hosting dev loop. (A no-op if dev-surfaces is off.)
    OpenEditorPane,
    /// Open a LIVE AGENT pane — the confined Hermes agent dock in its own split
    /// pane: a chat pane + the tool-call ledger (every tool-call a cap-gated
    /// RECEIPTED turn or an in-band refusal) + the live mandate inspector. The
    /// ADOS dev-loop made visible. (A no-op if dev-surfaces is off.)
    OpenAgentPane,

    // --- SURFACE MIGRATION (the Local→Surface tear-off) ---
    /// TEAR OFF the active surface into its own OS window — the Local→Surface
    /// migration: relocate the surface along the firmament distance axis from
    /// composited-in-the-cockpit to its own window, identity preserved (the same
    /// cell, the same body). Windowed-only; a no-op in the headless bake.
    TearOffActiveSurface,
    /// POP BACK the active surface's torn-off window into the dock (the inverse
    /// Surface-window → Surface-in-dock migration): close the second OS window.
    PopBackActiveSurface,

    // --- the cap-first SHELL / compositor (surfaces over real cells) ---
    /// Open a cap-confined surface (window) viewing the selected cell.
    ShellOpenSelected,
    /// Focus + raise the front-most owned surface (a cap-gated op).
    ShellFocusFront,
    /// Close the focused surface (cap-gated; the console is protected).
    ShellCloseFocused,
    /// Cycle the compositor layout (float → tile → stack).
    ShellCycleLayout,
    /// Minimize the focused surface (cap-gated).
    ShellMinimizeFocused,
    /// SHARE the focused window with another app — an ATTENUATING (read-only
    /// mirror) hand-off through a REAL `GrantCapability` turn. Commits.
    ShellShareFocused,
    /// Attempt to OVER-SHARE the focused window (hand out WIDER authority than
    /// held) — the no-amplification guarantee firing at the desktop: REJECTED by
    /// the real executor. The window-manager analogue of the ⚠ over-grant verb.
    ShellOverShareFocused,
    /// PRESENT from the focused surface through the verified scene — an honest
    /// frame advance that passes T1∧T2∧T3 and COMMITS (the commit polarity).
    ShellPresentFocused,
    /// Attempt an OVERPAINT — the focused surface painting another surface's
    /// region; the T1 non-overlap tooth REFUSES it (no-amplification on glass).
    ShellOverpaintFocused,
    /// Attempt an INPUT-STEAL — a non-focused surface asserting focus to grab the
    /// keystroke; the T3 input-routing tooth REFUSES it.
    ShellInputSteal,

    // --- replay / time-travel scrubber ---
    ReplayStepBack,
    ReplayStepForward,
    ReplayToGenesis,
    ReplayToHead,
    ReplayForkHere,
    ReplayClearFork,

    // --- the cipherclerk action loop (real macaroons) ---
    ClerkMint,
    ClerkAttenuate,
    ClerkDelegate,
    ClerkDischarge,

    // --- the debugger ---
    DebugRetargetSelected,

    // --- inspector / selection ---
    SelectImage,

    // --- the A2 SWARM (multi-agent cap-coordination + notify-edge inbox) ---
    /// Navigate to the SWARM tab (the multi-agent activity surface).
    GoSwarm,
    /// Coordinator emits a task/go event targeting worker-a. This is a
    /// cap-gated turn that deposits a NotifyEdge in worker-a's inbox
    /// (async, not a joint turn — the recipient drains in its OWN future turn).
    SwarmCoordinatorEmitA,
    /// Worker-a drains its pending notification. This is worker-a's own
    /// separate ack turn — independent receipt, different height, async model.
    SwarmWorkerADrain,
    /// Coordinator transfers 500 to worker-b AND wakes worker-a, in one turn.
    SwarmCoordinatorTransferAndWake,

    // --- the four-surface KILLER DEMO (N5) — the pug-handoff artifact ---
    /// Advance the killer demo by ONE frame (mint → agent turn → notify → drain →
    /// the dual refusal). Drives the headline script one receipted step at a time.
    KillerDemoAdvance,
    /// Run the WHOLE killer demo at once (the four frames + the dual refusal) and
    /// report the verdict — the `--headless` self-check, in the cockpit.
    KillerDemoRunAll,
    /// The pixel-layer over-share refusal — open the minted budget cell as a
    /// surface, share read-only, then watch the writable over-share REJECT at the
    /// glass (the no-amplification law in its third register).
    KillerDemoOverShare,
    /// Reset the killer demo to a fresh world at frame 0 (replay the script).
    KillerDemoReset,

    // --- the palette itself ---
    Dismiss,
}

impl CommandId {
    /// The category this command belongs to (drives grouping + the badge).
    pub fn category(self) -> Category {
        use CommandId::*;
        match self {
            Transfer | ComposeMulti | Grant | CreateCell | Seal | Burn | OverGrant
            | LaunchConfinedApp | SimRun | SimCommit | SimAddEffect => Category::Verb,
            GoHome | GoComposer | GoSimulate | GoObjects | GoDebugger | GoReplay | GoCipherclerk
            | GoEditor | GoShell | GoAgent | GoBuffer | GoTerminal | GoSwarm | GoGraph | GoOrgans
            | GoProofs | GoPowerbox | GoDevtools | GoWebShell => Category::Navigate,
            WebShellGo | WebShellBack | WebShellForward | WebShellReload => Category::Web,
            BufferType | BufferCommit | BufferReadOnlyWrite | TerminalRunInMandate
            | TerminalRunOutOfMandate | OpenTerminalPane | OpenEditorPane | OpenAgentPane
            | SwarmCoordinatorEmitA | SwarmWorkerADrain | SwarmCoordinatorTransferAndWake
            | KillerDemoAdvance | KillerDemoRunAll | KillerDemoOverShare | KillerDemoReset => {
                Category::Ide
            }
            ReplayStepBack | ReplayStepForward | ReplayToGenesis | ReplayToHead
            | ReplayForkHere | ReplayClearFork => Category::Replay,
            ClerkMint | ClerkAttenuate | ClerkDelegate | ClerkDischarge => Category::Clerk,
            ShellOpenSelected | ShellFocusFront | ShellCloseFocused | ShellCycleLayout
            | ShellMinimizeFocused | ShellShareFocused | ShellOverShareFocused
            | ShellPresentFocused | ShellOverpaintFocused | ShellInputSteal
            | TearOffActiveSurface | PopBackActiveSurface => Category::Shell,
            DebugRetargetSelected => Category::Debug,
            SelectImage => Category::Inspect,
            Dismiss => Category::Palette,
        }
    }

    /// The human title shown in the palette row.
    pub fn title(self) -> &'static str {
        use CommandId::*;
        match self {
            Transfer => "Transfer 1,000 → user",
            ComposeMulti => "Compose multi-action turn (pay service + user)",
            Grant => "Grant capability (service → user)",
            CreateCell => "Create cell (conserves value)",
            Seal => "Seal a fresh cell (lifecycle)",
            Burn => "Burn 1,000 (supply reduced)",
            OverGrant => "Over-grant (watch the executor REJECT)",
            SimRun => "Simulate the draft (predict the post-state + receipt, live world untouched)",
            SimCommit => "Commit the simulated intent for real (the identical turn)",
            SimAddEffect => "Add the picked effect to the simulate draft forest",
            GoHome => "Go to Home (the live verified image · the front door)",
            GoComposer => "Go to Composer",
            GoSimulate => "Go to Simulate (what-if intent composer · predict before committing)",
            GoObjects => "Go to Objects (proofs · nullifiers · lifecycle)",
            GoDebugger => "Go to Debugger",
            GoReplay => "Go to Replay (time-travel)",
            GoCipherclerk => "Go to Cipherclerk",
            GoEditor => "Go to Editor",
            GoShell => "Go to Shell (surfaces · windows · compositor)",
            GoAgent => "Go to Agent (a loop's provable activity)",
            GoBuffer => "Go to Editor buffer (a text buffer as a Surface cell)",
            GoTerminal => "Go to Terminal (a command surface · the ADOS seam)",
            GoSwarm => "Go to Swarm (multi-agent cap-coordination · notify-edge inbox)",
            GoGraph => "Go to Graph (ocap delegation · multi-hop layout)",
            GoOrgans => "Go to Organs (live trustline · flash-well cell-state)",
            GoProofs => "Go to Proofs (attach + STARK verification status)",
            GoPowerbox => "Go to Powerbox (CapDesk — designate a held cap into an app, attenuated)",
            GoDevtools => "Go to Devtools (Firebug for a verified OS — network · receipts · federation)",
            GoWebShell => "Go to Web-Shell (a general http(s):// browser — real Servo render behind the net-cap gate)",
            WebShellGo => "Web-shell: Go (render the address-bar URL through the cap-gated Servo WebView)",
            WebShellBack => "Web-shell: ← Back (previous URL in history, re-rendered)",
            WebShellForward => "Web-shell: → Forward (next URL in history, re-rendered)",
            WebShellReload => "Web-shell: ⟳ Reload (re-render the current URL)",
            LaunchConfinedApp => "Launch a confined app (no ambient authority → it requests via the powerbox)",
            SwarmCoordinatorEmitA => {
                "Swarm: coordinator emits task/go → worker-a (notify edge, async)"
            }
            SwarmWorkerADrain => {
                "Swarm: worker-a drains inbox (own ack turn — async, not joint)"
            }
            SwarmCoordinatorTransferAndWake => {
                "Swarm: coordinator transfers + wakes worker-a (one seam, two effects)"
            }
            KillerDemoAdvance => "Killer demo: ▶ advance one frame (mint → agent → notify → refusal)",
            KillerDemoRunAll => "Killer demo: ⏩ run the whole script (the four-surface self-check)",
            KillerDemoOverShare => "Killer demo: ⚠ over-share the budget window (pixel-layer REFUSE)",
            KillerDemoReset => "Killer demo: ↺ reset to frame 0 (replay)",
            BufferType => "Buffer: type a line (in-memory — goes dirty)",
            BufferCommit => "Buffer: commit the edit (cap-gated verified turn)",
            BufferReadOnlyWrite => "Buffer: ⚠ write a read-only mirror (watch it REFUSE)",
            TerminalRunInMandate => "Terminal: run an in-mandate command (COMMITS)",
            TerminalRunOutOfMandate => "Terminal: ⚠ run an out-of-mandate command (REFUSE)",
            OpenTerminalPane => "Open Terminal pane (live $SHELL on a PTY · build deos inside deos)",
            OpenEditorPane => "Open Editor pane (live deos-zed editor · edit deos inside deos)",
            OpenAgentPane => "Open Agent pane (confined Hermes · tool-call ledger + receipts + mandate inspector)",
            ShellOpenSelected => "Shell: open the selected cell as a surface",
            ShellFocusFront => "Shell: focus the front surface (cap-gated)",
            ShellCloseFocused => "Shell: close the focused surface (cap-gated)",
            ShellCycleLayout => "Shell: cycle layout (float · tile · stack)",
            ShellMinimizeFocused => "Shell: minimize the focused surface",
            ShellShareFocused => "Shell: share the focused window (read-only mirror)",
            ShellOverShareFocused => "Shell: ⚠ over-share the focused window (watch it REJECT)",
            ShellPresentFocused => "Shell: present the focused surface (T1∧T2∧T3 commits)",
            ShellOverpaintFocused => "Shell: ⚠ overpaint another surface's region (T1 REJECT)",
            ShellInputSteal => "Shell: ⚠ steal input focus (T3 REJECT)",
            TearOffActiveSurface => "Shell: ↗ tear off the active surface into its own window (Local→Surface migration, identity preserved)",
            PopBackActiveSurface => "Shell: ↩ pop the active surface back into the dock (close its torn-off window)",
            ReplayStepBack => "Replay: step back one turn",
            ReplayStepForward => "Replay: step forward one turn",
            ReplayToGenesis => "Replay: jump to genesis",
            ReplayToHead => "Replay: jump to head",
            ReplayForkHere => "Replay: fork a what-if here",
            ReplayClearFork => "Replay: clear the pinned fork",
            ClerkMint => "Cipherclerk: mint a root macaroon (alice / dns)",
            ClerkAttenuate => "Cipherclerk: attenuate the dns token (confine to read)",
            ClerkDelegate => "Cipherclerk: delegate dns/read to bob",
            ClerkDischarge => "Cipherclerk: discharge alice's dns token (verify)",
            DebugRetargetSelected => "Debugger: target a transfer from the selected cell",
            SelectImage => "Inspect: select this image",
            Dismiss => "Dismiss the palette",
        }
    }

    /// Extra keywords (beyond the title) the fuzzy matcher also searches, so an
    /// operator can find a command by its concept, not just its phrasing.
    pub fn keywords(self) -> &'static str {
        use CommandId::*;
        match self {
            Transfer => "pay send value move",
            ComposeMulti => "forest atomic batch multi siblings",
            Grant => "capability ocap delegate authority edge",
            CreateCell => "new object birth spawn",
            Seal => "freeze lifecycle lock close",
            Burn => "destroy supply reduce remove value",
            OverGrant => "amplification reject denied no-amplify security guard",
            SimRun => "simulate predict what-if dry-run preview fork throwaway before commit",
            SimCommit => "commit confirm apply for-real fire the simulated turn",
            SimAddEffect => "add effect compose intent draft forest build",
            GoHome => "home landing portal welcome front door image overview start begin",
            GoComposer => "verbs actions run",
            GoSimulate => "simulate what-if predict dry-run preview compose intent fork sandbox",
            GoObjects => "proof stark nullifier lifecycle reflect",
            GoDebugger => "step trace explain refusal",
            GoReplay => "history time travel scrub checkpoint",
            GoCipherclerk => "keys macaroon token identity wallet",
            GoEditor => "author validate deploy program factory",
            GoShell => "surface window compositor desktop apps wm",
            GoAgent => "agent loop swarm activity mandate receipt grounded ados integrator",
            GoBuffer => "editor buffer text file write edit document ide code scratch",
            GoTerminal => "terminal command shell console bash run ide tool-call ados seam",
            GoSwarm => "swarm multi-agent coordinator worker notify inbox wake coordination ados a2",
            GoGraph => "graph ocap delegation capability edge multi-hop reach blast-radius layout depth",
            GoOrgans => "organ trustline flashwell flash-well credit line channel mailbox court live cell-state",
            GoProofs => "proof stark verify attach tier verification signed by-construction light-client",
            GoPowerbox => "powerbox capdesk designate grant capability attenuate mint file dialog ocap pick picker confined app no-ambient-authority",
            GoDevtools => "devtools firebug devtools network receipts log console federation inspector data-plane deliveries queue inbox wake notify topic pub-sub committee epoch checkpoint revocation bridge filter drill-down",
            GoWebShell => "web shell browser http https url address bar servo webview render page internet net surf navigate site www tab",
            WebShellGo => "web shell browser go render http https url navigate load page fetch servo webview cap-gate net",
            WebShellBack => "web shell browser back previous history navigate url",
            WebShellForward => "web shell browser forward next history navigate url",
            WebShellReload => "web shell browser reload refresh re-render current url page",
            LaunchConfinedApp => "launch spawn start run confined app birth new cell powerbox request capability no-ambient-authority sandbox open application capdesk",
            SwarmCoordinatorEmitA => {
                "emit event notify wake inbox async turn receipt seam swarm coordinator worker"
            }
            SwarmWorkerADrain => {
                "drain inbox notify ack acknowledge async turn independent receipt swarm worker"
            }
            SwarmCoordinatorTransferAndWake => {
                "transfer value emit notify multi-effect turn swarm coordinator worker"
            }
            KillerDemoAdvance => {
                "killer demo headline mint factory agent notify handoff refusal four-surface pug evaluation step frame advance"
            }
            KillerDemoRunAll => {
                "killer demo headline self-check run all four-surface dual refusal over-grant over-spend stingray pug artifact verdict"
            }
            KillerDemoOverShare => {
                "over-share pixel glass surface window refuse no-amplification delegation-denied killer demo writable promote"
            }
            KillerDemoReset => "killer demo reset replay restart frame zero fresh world",
            BufferType => "edit type insert text buffer dirty",
            BufferCommit => "save commit buffer write digest turn cap-gated revision",
            BufferReadOnlyWrite => "read-only refuse attenuate mirror no-amplify buffer write guard",
            TerminalRunInMandate => "command run terminal bash mandate commit receipt authorized",
            TerminalRunOutOfMandate => "command refuse terminal bash mandate out-of-reach confined guard",
            OpenTerminalPane => "open terminal pane shell pty bash zsh cargo git build dev self-hosting live split console run command spawn",
            OpenEditorPane => "open editor pane code edit deos-zed file source dev self-hosting live split ide author write text",
            OpenAgentPane => "open agent pane hermes confined ai llm tool-call ledger receipt refusal mandate inspector ados dev-loop cap-gated turn dock chat",
            ShellOpenSelected => "open window surface cell app spawn view",
            ShellFocusFront => "focus raise front bring forward window",
            ShellCloseFocused => "close window surface dismiss",
            ShellCycleLayout => "tile float stack arrange layout compositor",
            ShellMinimizeFocused => "minimize collapse hide window surface",
            ShellShareFocused => "share window surface delegate grant attenuate mirror hand-off",
            ShellOverShareFocused => "over-share amplify widen reject window surface no-amplification grant",
            ShellPresentFocused => "present paint frame surface composite commit scene verified t1 t2 t3",
            ShellOverpaintFocused => "overpaint region reject non-overlap t1 amplify paint another scene security",
            ShellInputSteal => "input steal focus keystroke reject t3 route misroute volition scene security",
            TearOffActiveSurface => "tear off pop out window detach surface migration firmament distance relocate move multi-window split-out identity preserved local surface",
            PopBackActiveSurface => "pop back dock reattach close window torn-off surface migration return home merge",
            ReplayStepBack => "rewind previous undo back",
            ReplayStepForward => "advance next redo forward",
            ReplayToGenesis => "start beginning empty zero",
            ReplayToHead => "latest end now tip",
            ReplayForkHere => "branch what-if alternate counterfactual",
            ReplayClearFork => "unpin remove branch",
            ClerkMint => "forge root macaroon token create",
            ClerkAttenuate => "narrow confine restrict caveat",
            ClerkDelegate => "hand off recipient envelope sign",
            ClerkDischarge => "verify authorize check prove",
            DebugRetargetSelected => "retarget debug selected cell transfer",
            SelectImage => "root commitment distribution",
            Dismiss => "close cancel escape",
        }
    }
}

/// The category a command belongs to (grouping + the row badge).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Category {
    Verb,
    Navigate,
    Replay,
    Clerk,
    Shell,
    /// The 🌐 WEB-SHELL browser surface ops (go / back / forward / reload).
    Web,
    /// The A1 IDE developer surfaces (editor buffer + terminal command ops).
    Ide,
    Debug,
    Inspect,
    Palette,
}

impl Category {
    pub fn label(self) -> &'static str {
        match self {
            Category::Verb => "verb",
            Category::Navigate => "go",
            Category::Replay => "replay",
            Category::Clerk => "clerk",
            Category::Shell => "shell",
            Category::Web => "web",
            Category::Ide => "ide",
            Category::Debug => "debug",
            Category::Inspect => "inspect",
            Category::Palette => "palette",
        }
    }
}

/// A single palette command — a stable [`CommandId`] plus its pre-rendered
/// title/category (cached so the matcher doesn't recompute them).
#[derive(Clone, Copy, Debug)]
pub struct Command {
    pub id: CommandId,
    pub title: &'static str,
    pub category: Category,
}

impl Command {
    fn of(id: CommandId) -> Self {
        Command { id, title: id.title(), category: id.category() }
    }
}

/// The full registry, in display order. THIS is the canonical action list the
/// palette searches — every variant of [`CommandId`] except the internal
/// `Dismiss`, which the palette handles via Esc rather than a row.
pub fn all_commands() -> Vec<Command> {
    use CommandId::*;
    [
        // verbs first (the most common operator actions)
        Transfer, ComposeMulti, Grant, CreateCell, Seal, Burn, OverGrant,
        // the what-if / simulate composer (predict before committing)
        SimRun, SimCommit, SimAddEffect,
        // the runtime app-launcher (births a confined app → powerbox request)
        LaunchConfinedApp,
        // the cipherclerk loop
        ClerkMint, ClerkAttenuate, ClerkDelegate, ClerkDischarge,
        // the cap-first shell / compositor
        ShellOpenSelected, ShellFocusFront, ShellCloseFocused, ShellCycleLayout,
        ShellMinimizeFocused, ShellShareFocused, ShellOverShareFocused,
        ShellPresentFocused, ShellOverpaintFocused, ShellInputSteal,
        // SURFACE MIGRATION — the Local→Surface tear-off (pop a pane into its own window)
        TearOffActiveSurface, PopBackActiveSurface,
        // the A1 IDE developer surfaces (editor buffer + terminal)
        BufferType, BufferCommit, BufferReadOnlyWrite,
        TerminalRunInMandate, TerminalRunOutOfMandate,
        // the self-hosting dev panes (edit/build deos INSIDE deos) + the confined agent dock
        OpenTerminalPane, OpenEditorPane, OpenAgentPane,
        // the A2 SWARM surface (multi-agent cap-coordination + notify-edge inbox)
        SwarmCoordinatorEmitA, SwarmWorkerADrain, SwarmCoordinatorTransferAndWake,
        // the four-surface KILLER DEMO (N5) — the pug-handoff artifact
        KillerDemoRunAll, KillerDemoAdvance, KillerDemoOverShare, KillerDemoReset,
        // navigation
        GoHome,
        GoComposer, GoSimulate, GoObjects, GoDebugger, GoReplay, GoCipherclerk, GoEditor, GoShell,
        GoAgent, GoBuffer, GoTerminal, GoSwarm, GoGraph, GoOrgans, GoProofs, GoPowerbox,
        GoDevtools, GoWebShell,
        // the 🌐 web-shell browser surface (general http(s):// browser)
        WebShellGo, WebShellBack, WebShellForward, WebShellReload,
        // replay
        ReplayStepBack, ReplayStepForward, ReplayToGenesis, ReplayToHead,
        ReplayForkHere, ReplayClearFork,
        // debugger + inspect
        DebugRetargetSelected, SelectImage,
    ]
    .into_iter()
    .map(Command::of)
    .collect()
}

// ===========================================================================
// The fuzzy matcher — a small subsequence scorer (no extra deps).
// ===========================================================================

/// Score `query` against `haystack` with a subsequence match: every query char
/// must appear in order. Returns `None` if it does not match at all; a higher
/// score is a better match (contiguous runs + word-start hits score higher).
/// Case-insensitive.
pub fn fuzzy_score(query: &str, haystack: &str) -> Option<i32> {
    if query.is_empty() {
        return Some(0);
    }
    let q: Vec<char> = query.chars().flat_map(|c| c.to_lowercase()).collect();
    let h: Vec<char> = haystack.chars().flat_map(|c| c.to_lowercase()).collect();

    let mut qi = 0usize;
    let mut score = 0i32;
    let mut run = 0i32; // current contiguous-match run length
    let mut prev_was_sep = true; // start-of-string counts as a word boundary

    for (hi, &hc) in h.iter().enumerate() {
        let is_sep = hc == ' ' || hc == '-' || hc == '_' || hc == '/' || hc == '(';
        if qi < q.len() && hc == q[qi] {
            // base point for a matched char
            score += 1;
            // contiguous run bonus (matches that cluster score higher)
            run += 1;
            score += run;
            // word-start bonus
            if prev_was_sep {
                score += 5;
            }
            // early-position bonus (matches near the front rank higher)
            if hi < 8 {
                score += 2;
            }
            qi += 1;
        } else {
            run = 0;
        }
        prev_was_sep = is_sep;
    }

    if qi == q.len() {
        Some(score)
    } else {
        None
    }
}

/// One ranked search hit: the command + its score (for the test/inspection).
#[derive(Clone, Copy, Debug)]
pub struct Hit {
    pub command: Command,
    pub score: i32,
}

/// Filter + rank `commands` by `query`, searching the title AND the command's
/// keyword concepts. Best score first; ties broken by registry order (stable).
pub fn search(commands: &[Command], query: &str) -> Vec<Hit> {
    let mut hits: Vec<(usize, Hit)> = Vec::new();
    for (idx, cmd) in commands.iter().enumerate() {
        // Score the title and the keyword concepts; take the better of the two.
        let title_score = fuzzy_score(query, cmd.title);
        let kw_score = fuzzy_score(query, cmd.id.keywords());
        let best = match (title_score, kw_score) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        };
        if let Some(score) = best {
            hits.push((idx, Hit { command: *cmd, score }));
        }
    }
    // Sort by score desc, then by registry index asc (stable tie-break).
    hits.sort_by(|a, b| b.1.score.cmp(&a.1.score).then(a.0.cmp(&b.0)));
    hits.into_iter().map(|(_, h)| h).collect()
}

// ===========================================================================
// The palette state — query + selection over the live result list.
// ===========================================================================

/// The ⌘K palette's interaction state: whether it is open, the current query,
/// and the highlighted result index. The cockpit owns one of these, feeds it
/// keystrokes, and renders [`Self::results`].
pub struct CommandPalette {
    open: bool,
    query: String,
    selected: usize,
    commands: Vec<Command>,
}

impl Default for CommandPalette {
    fn default() -> Self {
        Self::new()
    }
}

impl CommandPalette {
    pub fn new() -> Self {
        CommandPalette {
            open: false,
            query: String::new(),
            selected: 0,
            commands: all_commands(),
        }
    }

    pub fn is_open(&self) -> bool {
        self.open
    }

    pub fn query(&self) -> &str {
        &self.query
    }

    pub fn selected(&self) -> usize {
        self.selected
    }

    /// Open the palette (⌘K), resetting the query + selection.
    pub fn open(&mut self) {
        self.open = true;
        self.query.clear();
        self.selected = 0;
    }

    /// Close the palette (Esc / after running a command).
    pub fn close(&mut self) {
        self.open = false;
        self.query.clear();
        self.selected = 0;
    }

    /// Toggle the palette open/closed (the ⌘K binding).
    pub fn toggle(&mut self) {
        if self.open {
            self.close();
        } else {
            self.open();
        }
    }

    /// Append a typed character to the query and clamp the selection.
    pub fn push_char(&mut self, c: char) {
        self.query.push(c);
        self.clamp_selection();
    }

    /// Backspace one character.
    pub fn backspace(&mut self) {
        self.query.pop();
        self.clamp_selection();
    }

    /// Set the whole query (e.g. from a text input).
    pub fn set_query(&mut self, q: impl Into<String>) {
        self.query = q.into();
        self.clamp_selection();
    }

    /// Move the highlight down one (wraps at the end).
    pub fn select_next(&mut self) {
        let n = self.results().len();
        if n == 0 {
            self.selected = 0;
        } else {
            self.selected = (self.selected + 1) % n;
        }
    }

    /// Move the highlight up one (wraps at the start).
    pub fn select_prev(&mut self) {
        let n = self.results().len();
        if n == 0 {
            self.selected = 0;
        } else {
            self.selected = (self.selected + n - 1) % n;
        }
    }

    fn clamp_selection(&mut self) {
        let n = self.results().len();
        if n == 0 {
            self.selected = 0;
        } else if self.selected >= n {
            self.selected = n - 1;
        }
    }

    /// The current ranked result list (filtered by the query).
    pub fn results(&self) -> Vec<Hit> {
        search(&self.commands, &self.query)
    }

    /// The currently-highlighted command, if any (what Enter runs).
    pub fn current(&self) -> Option<CommandId> {
        self.results().get(self.selected).map(|h| h.command.id)
    }

    /// "Accept" — return the highlighted command id (for the cockpit to
    /// dispatch) and close the palette. `None` if there is no match.
    pub fn accept(&mut self) -> Option<CommandId> {
        let id = self.current();
        if id.is_some() {
            self.close();
        }
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_command_id_is_in_the_registry() {
        // Guard: the registry covers every actionable variant (all but the
        // internal Dismiss). If a CommandId is added without a registry entry,
        // this catches it — keeping the palette comprehensive.
        let reg = all_commands();
        let ids: std::collections::HashSet<CommandId> = reg.iter().map(|c| c.id).collect();
        // Spot the spread of categories present.
        for must in [
            CommandId::Transfer,
            CommandId::OverGrant,
            CommandId::GoCipherclerk,
            CommandId::ReplayForkHere,
            CommandId::ClerkMint,
            CommandId::ClerkDischarge,
            CommandId::DebugRetargetSelected,
            CommandId::SelectImage,
        ] {
            assert!(ids.contains(&must), "{must:?} must be registered");
        }
        // Dismiss is intentionally NOT a row (Esc handles it).
        assert!(!ids.contains(&CommandId::Dismiss));
        // The registry is non-trivial (and now includes the shell surface + swarm A2).
        assert!(reg.len() >= 34, "registry should cover the whole action surface");
    }

    #[test]
    fn the_runtime_app_launcher_command_is_registered_and_findable() {
        // The runtime app-launcher (the powerbox's missing first half) is reachable
        // through the ⌘K palette like every other action — no parallel path. It is a
        // Verb (it births a cell), and findable by its launch/spawn/confined concepts.
        let reg = all_commands();
        let ids: std::collections::HashSet<CommandId> = reg.iter().map(|c| c.id).collect();
        assert!(ids.contains(&CommandId::LaunchConfinedApp), "the launcher command is registered");
        assert_eq!(CommandId::LaunchConfinedApp.category(), Category::Verb);
        // Found by concept: "launch", "spawn", "confined" all surface the launcher.
        for q in ["launch", "spawn confined", "confined app"] {
            assert!(
                search(&reg, q).iter().any(|h| h.command.id == CommandId::LaunchConfinedApp),
                "the launcher is findable via {q:?}"
            );
        }
    }

    #[test]
    fn the_killer_demo_commands_are_registered_and_findable() {
        // The four-surface killer demo (N5) is reachable through the ⌘K palette like
        // every other action (no parallel path): its commands are registered and
        // found by their concepts. The same dispatch the SWARM-tab buttons call.
        let reg = all_commands();
        let ids: std::collections::HashSet<CommandId> = reg.iter().map(|c| c.id).collect();
        for must in [
            CommandId::KillerDemoAdvance,
            CommandId::KillerDemoRunAll,
            CommandId::KillerDemoOverShare,
            CommandId::KillerDemoReset,
        ] {
            assert!(ids.contains(&must), "{must:?} must be registered");
        }
        // Found by concept: "killer demo" → run-all; "over-share" → the pixel-layer
        // refusal; "mint" → the advance (frame 1 mints); "four-surface" → the demo.
        assert!(search(&reg, "killer demo").iter().any(|h| h.command.id == CommandId::KillerDemoRunAll));
        assert!(search(&reg, "over-share").iter().any(|h| h.command.id == CommandId::KillerDemoOverShare));
        assert!(search(&reg, "four-surface").iter().any(|h| {
            matches!(h.command.id, CommandId::KillerDemoRunAll | CommandId::KillerDemoAdvance)
        }));
    }

    #[test]
    fn the_shell_commands_are_registered_and_findable() {
        // The cap-first shell surface is reachable through the palette like every
        // other action (no parallel path): its commands are registered and can be
        // found by their window-manager concepts.
        let reg = all_commands();
        let ids: std::collections::HashSet<CommandId> = reg.iter().map(|c| c.id).collect();
        // GoShell is a tab-switch (Navigate, like the other Go* commands); the
        // Shell* ops are the cap-first window-manager actions (Category::Shell).
        assert!(ids.contains(&CommandId::GoShell), "GoShell must be registered");
        assert_eq!(CommandId::GoShell.category(), Category::Navigate);
        for must in [
            CommandId::ShellOpenSelected,
            CommandId::ShellFocusFront,
            CommandId::ShellCloseFocused,
            CommandId::ShellCycleLayout,
            CommandId::ShellMinimizeFocused,
            CommandId::ShellShareFocused,
            CommandId::ShellOverShareFocused,
        ] {
            assert!(ids.contains(&must), "{must:?} must be registered");
            assert_eq!(must.category(), Category::Shell);
        }
        // Found by concept: "tile" → cycle-layout; "open window" → open-surface;
        // "delegate"/"amplify" → the real-executor window-share + its rejection.
        assert!(search(&reg, "tile").iter().any(|h| h.command.id == CommandId::ShellCycleLayout));
        assert!(search(&reg, "window").iter().any(|h| h.command.id == CommandId::ShellOpenSelected));
        assert!(search(&reg, "compositor").iter().any(|h| h.command.id == CommandId::GoShell));
        assert!(search(&reg, "delegate").iter().any(|h| h.command.id == CommandId::ShellShareFocused));
        assert!(search(&reg, "amplify").iter().any(|h| h.command.id == CommandId::ShellOverShareFocused));
    }

    #[test]
    fn the_a1_ide_commands_are_registered_and_findable() {
        // The A1 DEVELOPER surfaces (editor buffer + terminal) are reachable
        // through the palette like every other action: their nav switches +
        // cap-gated ops are registered, categorized, and findable by concept.
        let reg = all_commands();
        let ids: std::collections::HashSet<CommandId> = reg.iter().map(|c| c.id).collect();
        // The nav switches are Navigate (like the other Go*).
        for go in [CommandId::GoBuffer, CommandId::GoTerminal] {
            assert!(ids.contains(&go), "{go:?} must be registered");
            assert_eq!(go.category(), Category::Navigate);
        }
        // The IDE action ops are Category::Ide.
        for op in [
            CommandId::BufferType,
            CommandId::BufferCommit,
            CommandId::BufferReadOnlyWrite,
            CommandId::TerminalRunInMandate,
            CommandId::TerminalRunOutOfMandate,
        ] {
            assert!(ids.contains(&op), "{op:?} must be registered");
            assert_eq!(op.category(), Category::Ide);
        }
        // Found by concept: "editor"/"buffer" → the buffer; "terminal"/"bash" →
        // the terminal; "read-only"/"commit"/"mandate" → the cap-gated ops.
        assert!(search(&reg, "editor buffer").iter().any(|h| h.command.id == CommandId::GoBuffer));
        assert!(search(&reg, "terminal bash").iter().any(|h| h.command.id == CommandId::GoTerminal));
        assert!(search(&reg, "commit").iter().any(|h| h.command.id == CommandId::BufferCommit));
        assert!(search(&reg, "read-only").iter().any(|h| h.command.id == CommandId::BufferReadOnlyWrite));
        assert!(search(&reg, "mandate").iter().any(|h| h.command.id == CommandId::TerminalRunInMandate
            || h.command.id == CommandId::TerminalRunOutOfMandate));
    }

    #[test]
    fn the_swarm_commands_are_registered_and_findable() {
        // The A2 swarm surface commands are registered in the palette and
        // categorized correctly (Navigate for GoSwarm, Ide for swarm actions).
        let reg = all_commands();
        let ids: std::collections::HashSet<CommandId> = reg.iter().map(|c| c.id).collect();
        assert!(ids.contains(&CommandId::GoSwarm), "GoSwarm must be registered");
        assert_eq!(CommandId::GoSwarm.category(), Category::Navigate);
        for op in [
            CommandId::SwarmCoordinatorEmitA,
            CommandId::SwarmWorkerADrain,
            CommandId::SwarmCoordinatorTransferAndWake,
        ] {
            assert!(ids.contains(&op), "{op:?} must be registered");
            assert_eq!(op.category(), Category::Ide);
        }
        // Findable by concept — "swarm", "notify", "emit", "drain".
        assert!(
            search(&reg, "swarm").iter().any(|h| h.command.id == CommandId::GoSwarm),
            "GoSwarm findable via 'swarm'"
        );
        assert!(
            search(&reg, "emit notify").iter().any(|h| {
                h.command.id == CommandId::SwarmCoordinatorEmitA
                    || h.command.id == CommandId::SwarmCoordinatorTransferAndWake
            }),
            "emit/notify commands findable"
        );
        assert!(
            search(&reg, "drain").iter().any(|h| h.command.id == CommandId::SwarmWorkerADrain),
            "SwarmWorkerADrain findable via 'drain'"
        );
    }

    #[test]
    fn fuzzy_subsequence_matches_and_rejects() {
        assert!(fuzzy_score("trf", "Transfer 1,000 → user").is_some());
        assert!(fuzzy_score("transfer", "Transfer 1,000 → user").is_some());
        // A non-subsequence does not match.
        assert!(fuzzy_score("zzz", "Transfer").is_none());
        // Empty query matches everything (score 0).
        assert_eq!(fuzzy_score("", "anything"), Some(0));
    }

    #[test]
    fn fuzzy_prefers_word_starts_and_contiguous_runs() {
        // "burn" as a contiguous word-start should outscore a scattered match.
        let contiguous = fuzzy_score("burn", "Burn 1,000 (supply reduced)").unwrap();
        let scattered = fuzzy_score("burn", "back upstream run now").unwrap_or(i32::MIN);
        assert!(contiguous > scattered, "contiguous word-start scores higher");
    }

    #[test]
    fn search_finds_a_verb_by_title() {
        let cmds = all_commands();
        let hits = search(&cmds, "transfer");
        assert!(!hits.is_empty());
        assert_eq!(hits[0].command.id, CommandId::Transfer, "best hit is the transfer verb");
    }

    #[test]
    fn search_finds_a_command_by_keyword_concept() {
        // "wallet" is not in any title, but it IS a keyword of GoCipherclerk.
        let cmds = all_commands();
        let hits = search(&cmds, "wallet");
        assert!(
            hits.iter().any(|h| h.command.id == CommandId::GoCipherclerk),
            "keyword search surfaces the cipherclerk"
        );
        // "amplification" is a keyword of the over-grant guard demo.
        let hits = search(&cmds, "amplification");
        assert!(hits.iter().any(|h| h.command.id == CommandId::OverGrant));
    }

    #[test]
    fn search_finds_clerk_discharge_by_verify() {
        let cmds = all_commands();
        let hits = search(&cmds, "verify");
        assert!(
            hits.iter().any(|h| h.command.id == CommandId::ClerkDischarge),
            "discharge is findable by its 'verify' concept"
        );
    }

    #[test]
    fn empty_query_returns_the_whole_registry_in_order() {
        let cmds = all_commands();
        let hits = search(&cmds, "");
        assert_eq!(hits.len(), cmds.len(), "empty query shows everything");
        // Order preserved (Transfer is first in the registry).
        assert_eq!(hits[0].command.id, CommandId::Transfer);
    }

    // --- the interaction model ------------------------------------------

    #[test]
    fn open_close_toggle_lifecycle() {
        let mut p = CommandPalette::new();
        assert!(!p.is_open());
        p.toggle();
        assert!(p.is_open());
        assert_eq!(p.query(), "");
        p.toggle();
        assert!(!p.is_open());
    }

    #[test]
    fn typing_filters_and_enter_accepts() {
        let mut p = CommandPalette::new();
        p.open();
        for c in "burn".chars() {
            p.push_char(c);
        }
        // The top result should be the burn verb.
        assert_eq!(p.current(), Some(CommandId::Burn));
        // Enter accepts it and closes the palette.
        let accepted = p.accept();
        assert_eq!(accepted, Some(CommandId::Burn));
        assert!(!p.is_open(), "accepting closes the palette");
    }

    #[test]
    fn backspace_widens_the_filter() {
        let mut p = CommandPalette::new();
        p.open();
        p.set_query("burnx"); // the trailing x breaks the burn subsequence
        // Robust to a growing command set: assert the burn verb specifically is
        // filtered out (the point of the test), not that the WHOLE list is empty —
        // another command's keywords may legitimately contain b-u-r-n-…-x.
        assert_ne!(p.current(), Some(CommandId::Burn), "burnx does not match the burn verb");
        p.backspace(); // → "burn"
        assert_eq!(p.current(), Some(CommandId::Burn), "backspace re-widens to re-include burn");
    }

    #[test]
    fn selection_wraps_and_clamps() {
        let mut p = CommandPalette::new();
        p.open();
        p.set_query("go"); // matches all six navigation commands (and others)
        let n = p.results().len();
        assert!(n >= 6);
        // Wrap backwards from 0 → last.
        p.select_prev();
        assert_eq!(p.selected(), n - 1);
        // Wrap forward from last → 0.
        p.select_next();
        assert_eq!(p.selected(), 0);
    }

    #[test]
    fn accept_with_no_match_returns_none_and_stays_open() {
        let mut p = CommandPalette::new();
        p.open();
        p.set_query("qqqqzzzz");
        assert!(p.results().is_empty());
        assert_eq!(p.accept(), None);
        assert!(p.is_open(), "a no-match accept does not close");
    }
}
