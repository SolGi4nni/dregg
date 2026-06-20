//! THE TERMINAL SURFACE — a command surface as a cap-confined Surface cell.
//!
//! The second DEVELOPER content surface of the dregg IDE (A1) and **the place
//! the ADOS A0 tool-call seam will live**: an agent's `Bash`/command, routed
//! through a terminal-cell's capability. `docs/DREGG-DESKTOP-OS.md` §1 + the
//! agent-activity surface (`crate::agent`) cast the integrator wedge as grounding
//! *the agent's ACTIONS, at the tool-call/turn boundary* — and a terminal IS
//! that boundary made a surface: a command is a cap-gated action; the
//! terminal-cell holds the cap for **what it may run / touch**; the output is
//! the surface's content.
//!
//! **The terminal is backed by a REAL cell** whose c-list IS the command
//! authority. A command names a TARGET cell (the cell it acts upon); running it
//! is gated by whether the terminal-cell holds a capability reaching that target
//! — the SAME ocap question the executor's no-amplification rule answers, read
//! from the live ledger (`Capabilities::has_access`). A command whose target is
//! OUTSIDE the terminal-cell's caps is REFUSED (the agent's `Bash` confined to
//! its mandate); an authorized command runs as a REAL verified turn through
//! [`World::commit_turn`] and its RECEIPT is the output line (the grounded-seam
//! receipt the agent-activity surface already renders, here at the prompt).
//!
//! The COMMAND CAP-GATE is the A1 seam: for A1 the actual exec is host/stubbed —
//! the point is the cap-gating + the receipt. A command is one of a small typed
//! vocabulary (`transfer` value, `grant` a cap, `set` a field, `emit` an event),
//! each mapping to a real [`Effect`] the executor runs; the terminal's job is to
//! REFUSE the ones the terminal-cell has no cap for and to RECEIPT the ones it
//! does. (The eventual ADOS seam swaps the typed verb for a routed host
//! `Bash`/tool-call whose effects flow through this same gate.)
//!
//! Two gates compose (mirroring [`crate::shell::Shell::present`] +
//! [`crate::buffer::BufferCell::commit`]):
//!   1. THE COMMAND CAP-GATE — the terminal-cell must hold authority reaching the
//!      command's target ([`TerminalCell::is_command_authorized`]); an
//!      out-of-mandate command is REFUSED here, BEFORE any turn (fail-closed).
//!   2. THE EXECUTOR GATE — the authorized command runs as a real turn (the
//!      executor's `Permissions` + whole-turn guarantees apply); its receipt is
//!      the committed output.
//!
//! This module is gpui-FREE and `cargo test`-able (the terminal model is built
//! purely from the `World`). The cockpit maps [`TerminalView`] onto a simple
//! gpui terminal panel (the IDE's terminal pane).

use dregg_cell::CellId;

use crate::world::{self, World};

/// A typed terminal command — the small vocabulary the A1 terminal routes. Each
/// names a TARGET cell (what it acts upon) and maps to a real [`Effect`](dregg_turn::action::Effect)
/// the executor runs IFF the terminal-cell holds a cap reaching that target.
/// (The ADOS seam will swap this for a routed host `Bash`/tool-call; the
/// cap-gate + receipt shape is identical.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    /// `transfer <amount> -> <target>` — move value from the terminal-cell to
    /// `target` (gated: the terminal-cell must reach `target`).
    Transfer { target: CellId, amount: u64 },
    /// `grant <slot> -> <target>` — grant the terminal-cell itself a cap reaching
    /// `target` at a fresh slot (gated: it must ALREADY reach `target`, the
    /// no-amplification rule — you can only re-grant what you hold).
    Grant { target: CellId, slot: u32 },
    /// `set <index> <value> @ <target>` — write a field on `target` (gated: the
    /// terminal-cell must reach `target`).
    SetField { target: CellId, index: usize, value: u8 },
    /// `emit <topic> @ <target>` — emit an event on `target` (gated: reach).
    Emit { target: CellId, topic: String },
}

impl Command {
    /// The TARGET cell this command acts upon — the cell the command-cap gate
    /// checks the terminal-cell's reach against.
    pub fn target(&self) -> CellId {
        match self {
            Command::Transfer { target, .. }
            | Command::Grant { target, .. }
            | Command::SetField { target, .. }
            | Command::Emit { target, .. } => *target,
        }
    }

    /// The command verb (operator-legible — the prompt echoes it).
    pub fn verb(&self) -> &'static str {
        match self {
            Command::Transfer { .. } => "transfer",
            Command::Grant { .. } => "grant",
            Command::SetField { .. } => "set",
            Command::Emit { .. } => "emit",
        }
    }

    /// The shell-style command line (what the operator typed / the prompt shows).
    pub fn line(&self) -> String {
        match self {
            Command::Transfer { target, amount } => {
                format!("transfer {amount} -> {}", crate::reflect::short_hex(target.as_bytes()))
            }
            Command::Grant { target, slot } => {
                format!("grant slot{slot} -> {}", crate::reflect::short_hex(target.as_bytes()))
            }
            Command::SetField { target, index, value } => format!(
                "set field[{index}]={value} @ {}",
                crate::reflect::short_hex(target.as_bytes())
            ),
            Command::Emit { target, topic } => {
                format!("emit '{topic}' @ {}", crate::reflect::short_hex(target.as_bytes()))
            }
        }
    }

    /// Lower the command to the real [`Effect`](dregg_turn::action::Effect) the
    /// executor runs (from the terminal-cell `from`). This is what a committed,
    /// authorized command actually does — a genuine protocol effect, not a mock.
    fn to_effect(&self, from: CellId) -> dregg_turn::action::Effect {
        match self {
            Command::Transfer { target, amount } => world::transfer(from, *target, *amount),
            // Re-grant the terminal-cell's existing reach to `target` at `slot`
            // (the executor enforces no-amplification: it must hold the cap).
            Command::Grant { target, slot } => world::grant_capability(from, from, *target, *slot),
            Command::SetField { target, index, value } => {
                let mut fe = [0u8; 32];
                fe[31] = *value;
                world::set_field(*target, *index, fe)
            }
            Command::Emit { target, topic } => world::emit_event(*target, topic, vec![]),
        }
    }
}

/// Why a command was REFUSED. Each variant is a tooth of the terminal's ocap
/// discipline firing — a refusal changes NOTHING (fail-closed), surfaced so the
/// operator (or the agent watching its own confined terminal) sees WHY.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandError {
    /// **THE OUT-OF-MANDATE TOOTH** — the terminal-cell holds NO capability
    /// reaching the command's target. The command is REFUSED by the command
    /// cap-gate BEFORE any turn runs: an agent's `Bash` confined to its mandate
    /// cannot touch a cell it has no cap for. Carries the target (for the log).
    OutOfMandate { target: CellId },
    /// The terminal's backing cell is gone from the ledger (a dangling terminal).
    Unbacked,
    /// The authorized command's turn was REJECTED by the real executor (its
    /// `Permissions`, balance, or a whole-turn guarantee fired). Carries the
    /// executor's reason. (Distinct from `OutOfMandate`, which is the cap-gate
    /// refusing BEFORE any turn.)
    ExecutorRejected(String),
}

impl CommandError {
    /// A short operator-legible label (the tooth that bit).
    pub fn tooth(&self) -> &'static str {
        match self {
            CommandError::OutOfMandate { .. } => "out-of-mandate",
            CommandError::Unbacked => "unbacked",
            CommandError::ExecutorRejected(_) => "executor-rejected",
        }
    }

    /// A one-line human explanation (the prompt surfaces this as the refusal).
    pub fn explain(&self) -> String {
        match self {
            CommandError::OutOfMandate { target } => format!(
                "REFUSED — the terminal-cell holds no capability reaching {} (this command is \
                 outside the terminal's mandate; the agent's Bash is confined to its caps)",
                crate::reflect::short_hex(target.as_bytes())
            ),
            CommandError::Unbacked => {
                "REFUSED — the terminal's backing cell is gone from the ledger (dangling)"
                    .to_string()
            }
            CommandError::ExecutorRejected(why) => format!("REFUSED by the executor — {why}"),
        }
    }
}

/// One line in the terminal's output history — a command and its outcome. A
/// committed command carries the REAL receipt hash (the grounded-seam receipt,
/// at the prompt); a refused one carries the refusal reason (never faked). This
/// IS the terminal's content (the surface body).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutputLine {
    /// The command line the operator/agent issued (echoed at the prompt).
    pub command: String,
    /// Whether the executor COMMITTED it (a refused command is shown as such).
    pub committed: bool,
    /// The receipt hash (the provenance link), if committed — the output IS the
    /// receipt, the same truth the agent-activity surface renders.
    pub receipt_hash: Option<[u8; 32]>,
    /// The computrons the executor metered (the command's real cost), if any.
    pub computrons: u64,
    /// A human-meaningful result / refusal reason (the visible output text).
    pub result: String,
}

impl OutputLine {
    /// A short hex of the receipt (the prompt's provenance pill), if committed.
    pub fn receipt_short(&self) -> Option<String> {
        self.receipt_hash.map(|h| crate::reflect::short_hex(&h))
    }
}

/// THE TERMINAL SURFACE — a command surface as a cap-confined Surface cell.
///
/// Binds a [`SurfaceId`](crate::surface::SurfaceId) (the terminal's window handle
/// in the shell) + the backing cell whose c-list IS the command authority + an
/// append-only output history (the surface's content). The cockpit composites it
/// like any other surface; the panel body renders the output lines + the prompt.
///
/// This is distinct from a plain cell-view: a terminal surface's body is COMMAND
/// OUTPUT (receipts), and its authority over what it may run is the terminal-
/// cell's real c-list — the §7 cap model carried to a command line, and the home
/// of the ADOS A0 tool-call seam.
#[derive(Clone, Debug)]
pub struct TerminalCell {
    /// The shell surface id this terminal renders into (its window handle).
    surface: crate::surface::SurfaceId,
    /// The backing cell whose CAPABILITIES are the command authority + who acts
    /// as `from` for every command's effect. The REAL anchor in the live ledger.
    backing: CellId,
    /// The append-only output history (the surface content — commands + their
    /// receipts/refusals, oldest-first).
    history: Vec<OutputLine>,
    /// An operator-facing terminal name (the panel title).
    name: String,
}

impl TerminalCell {
    /// Open a fresh terminal over `backing` (the cell whose c-list is the command
    /// authority + who acts as `from`), rendering into shell surface `surface`.
    pub fn new(
        surface: crate::surface::SurfaceId,
        backing: CellId,
        name: impl Into<String>,
    ) -> Self {
        TerminalCell {
            surface,
            backing,
            history: Vec::new(),
            name: name.into(),
        }
    }

    /// The shell surface id (window handle).
    pub fn surface(&self) -> crate::surface::SurfaceId {
        self.surface
    }

    /// The backing cell id (the command-authority anchor + `from`).
    pub fn backing(&self) -> CellId {
        self.backing
    }

    /// The terminal name (panel title).
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The output history (oldest-first — the surface content).
    pub fn history(&self) -> &[OutputLine] {
        &self.history
    }

    /// **THE COMMAND CAP-GATE.** Whether the terminal-cell is AUTHORIZED to run
    /// `cmd` — i.e. its backing cell holds a capability reaching the command's
    /// target (read from the LIVE ledger via `Capabilities::has_access`). This is
    /// the ocap question the ADOS seam asks of an agent's `Bash`: is this action
    /// within the terminal-cell's mandate? A self-targeting command (the terminal
    /// acting on its OWN cell) is always authorized — a cell reaches itself.
    pub fn is_command_authorized(&self, world: &World, cmd: &Command) -> bool {
        let target = cmd.target();
        if target == self.backing {
            return true; // a cell always reaches itself (its own mandate).
        }
        world
            .ledger()
            .get(&self.backing)
            .map(|c| c.capabilities.has_access(&target))
            .unwrap_or(false)
    }

    /// The set of target cells this terminal may reach (its mandate, for the
    /// panel's "authorized targets" badge). The backing cell + every cap target.
    pub fn reachable(&self, world: &World) -> Vec<CellId> {
        let mut out = vec![self.backing];
        if let Some(c) = world.ledger().get(&self.backing) {
            for cap in c.capabilities.iter() {
                if !out.contains(&cap.target) {
                    out.push(cap.target);
                }
            }
        }
        out
    }

    /// **RUN A COMMAND — the cap-gated, receipted action (the ADOS seam).**
    /// Two gates fire, in order:
    ///   1. THE COMMAND CAP-GATE — the terminal-cell must reach `cmd`'s target
    ///      ([`Self::is_command_authorized`]); an out-of-mandate command is
    ///      REFUSED here ([`CommandError::OutOfMandate`]) BEFORE any turn runs
    ///      (fail-closed — the agent's Bash confined to its caps).
    ///   2. THE EXECUTOR GATE — the authorized command runs as a REAL turn (the
    ///      effect lowered from `cmd`, acting as the terminal-cell); a rejection
    ///      surfaces as [`CommandError::ExecutorRejected`].
    ///
    /// On success an [`OutputLine`] carrying the REAL receipt is appended to the
    /// history (the output IS the receipt — the grounded seam at the prompt). A
    /// refusal appends a REFUSED line (never faked) and changes no state. Returns
    /// the appended line either way (so the prompt always echoes the outcome).
    pub fn run(&mut self, world: &mut World, cmd: Command) -> Result<OutputLine, CommandError> {
        let line_text = cmd.line();

        // The backing cell must be live (a dangling terminal cannot run).
        if world.ledger().get(&self.backing).is_none() {
            let err = CommandError::Unbacked;
            self.push_refused(&line_text, &err);
            return Err(err);
        }

        // (1) THE COMMAND CAP-GATE — is the target within the terminal's mandate?
        if !self.is_command_authorized(world, &cmd) {
            let err = CommandError::OutOfMandate { target: cmd.target() };
            self.push_refused(&line_text, &err);
            return Err(err);
        }

        // (2) THE EXECUTOR GATE — run the command as a REAL verified turn.
        let effect = cmd.to_effect(self.backing);
        let turn = world.turn(self.backing, vec![effect]);
        match world.commit_turn(turn) {
            crate::CommitOutcome::Committed { receipt, .. } => {
                let line = OutputLine {
                    command: line_text,
                    committed: true,
                    receipt_hash: Some(receipt.receipt_hash()),
                    computrons: receipt.computrons_used,
                    result: format!(
                        "ok · {} action(s) · receipt {}",
                        receipt.action_count,
                        crate::reflect::short_hex(&receipt.receipt_hash())
                    ),
                };
                self.history.push(line.clone());
                Ok(line)
            }
            crate::CommitOutcome::Rejected { reason, .. } => {
                let err = CommandError::ExecutorRejected(reason);
                let line = self.push_refused(&line_text, &err);
                // Return the line so the caller can echo it; the error too.
                let _ = line;
                Err(err)
            }
            // The world is suspended (meta-debug): the command's turn staged, did
            // not run. Surfaced as a refused line (fail-closed, never faked ok).
            crate::CommitOutcome::Queued { .. } => {
                let err = CommandError::ExecutorRejected(
                    "world suspended: turn queued, not committed".to_string(),
                );
                let _ = self.push_refused(&line_text, &err);
                Err(err)
            }
        }
    }

    /// Append a REFUSED output line (the ocap/verification guarantee firing,
    /// never faked). Returns the appended line.
    fn push_refused(&mut self, command: &str, err: &CommandError) -> OutputLine {
        let line = OutputLine {
            command: command.to_string(),
            committed: false,
            receipt_hash: None,
            computrons: 0,
            result: err.explain(),
        };
        self.history.push(line.clone());
        line
    }
}

/// THE TERMINAL VIEW — the gpui-free render model the cockpit maps onto its
/// terminal pane. Built purely from a [`TerminalCell`] + the live [`World`], so
/// the panel shows the terminal's real authority (its reachable targets) + its
/// real output (receipts) — never a self-report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TerminalView {
    /// The terminal name (panel title).
    pub name: String,
    /// A short id for the backing cell (the command-authority anchor).
    pub backing_short: String,
    /// Whether the backing cell is present in the live ledger.
    pub backed: bool,
    /// Short ids of the targets this terminal may reach (its mandate badge).
    pub reachable_short: Vec<String>,
    /// The number of committed commands (the terminal's grounded action count).
    pub committed_count: usize,
    /// The output history (oldest-first — the terminal body, commands + results).
    pub lines: Vec<OutputLine>,
}

impl TerminalView {
    /// Build the view from a terminal + the live world.
    pub fn build(term: &TerminalCell, world: &World) -> Self {
        let backed = world.ledger().get(&term.backing).is_some();
        let reachable_short = term
            .reachable(world)
            .iter()
            .map(|c| crate::reflect::short_hex(c.as_bytes()))
            .collect();
        let committed_count = term.history.iter().filter(|l| l.committed).count();
        TerminalView {
            name: term.name.clone(),
            backing_short: crate::reflect::short_hex(term.backing.as_bytes()),
            backed,
            reachable_short,
            committed_count,
            lines: term.history.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shell::Shell;

    /// A world + shell + a terminal whose backing cell HOLDS a cap reaching a
    /// peer (its mandate), plus the peer it may touch + a stranger it may not.
    fn terminal_world() -> (World, TerminalCell, CellId, CellId) {
        let mut world = World::new();
        let peer = world.genesis_cell(0x70, 0);
        let stranger = world.genesis_cell(0x71, 0);
        // The terminal-cell is born holding a cap reaching `peer` (its mandate),
        // funded so a transfer can succeed at the executor gate.
        let (backing, _slot) = world.genesis_cell_with_cap(0x72, 10_000, peer);
        let mut shell = Shell::new();
        let cap = shell.open_cell_view(backing, "term");
        let term = TerminalCell::new(cap.surface(), backing, "term");
        (world, term, peer, stranger)
    }

    #[test]
    fn the_command_lowers_to_a_real_effect_and_names_its_target() {
        let t = CellId::from_bytes([7u8; 32]);
        let cmd = Command::Transfer { target: t, amount: 100 };
        assert_eq!(cmd.target(), t);
        assert_eq!(cmd.verb(), "transfer");
        assert!(cmd.line().contains("transfer 100"));
    }

    // ── THE AUTHORIZED POLARITY: an in-mandate command runs + receipts ──

    #[test]
    fn an_in_mandate_command_runs_as_a_real_turn_and_receipts() {
        // THE GROUNDED SEAM: a command whose target IS within the terminal-cell's
        // mandate (it holds a cap reaching `peer`) runs as a REAL verified turn,
        // and its RECEIPT is the output line (the agent-activity grounded seam, at
        // the prompt).
        let (mut world, mut term, peer, _stranger) = terminal_world();
        assert!(
            term.is_command_authorized(&world, &Command::Transfer { target: peer, amount: 1 }),
            "the terminal-cell reaches the peer (its mandate)"
        );
        let h0 = world.height();
        let line = term
            .run(&mut world, Command::Transfer { target: peer, amount: 1_000 })
            .expect("an in-mandate command commits");
        assert!(line.committed, "the command committed");
        assert!(line.receipt_hash.is_some(), "the output IS a real receipt");
        assert_eq!(world.height(), h0 + 1, "a real turn was committed");
        // The value moved (the effect is real, not a mock).
        assert_eq!(world.ledger().get(&peer).unwrap().state.balance(), 1_000);
        // The history records it.
        assert_eq!(term.history().len(), 1);
        assert!(term.history()[0].committed);
    }

    #[test]
    fn a_self_targeting_command_is_always_in_mandate() {
        // A command acting on the terminal's OWN cell is always authorized (a
        // cell reaches itself) — e.g. setting a field on the backing cell.
        let (mut world, mut term, _peer, _stranger) = terminal_world();
        let backing = term.backing();
        let line = term
            .run(&mut world, Command::SetField { target: backing, index: 3, value: 9 })
            .expect("a self-targeting set commits");
        assert!(line.committed);
        assert_eq!(world.ledger().get(&backing).unwrap().state.fields[3][31], 9);
    }

    // ── THE OUT-OF-MANDATE POLARITY: a command outside the cap REFUSES ──

    #[test]
    fn a_command_outside_the_terminals_cap_is_refused() {
        // THE OUT-OF-MANDATE TOOTH: a command targeting a STRANGER cell the
        // terminal-cell holds NO cap for is REFUSED by the command cap-gate BEFORE
        // any turn runs (fail-closed — the agent's Bash confined to its mandate).
        let (mut world, mut term, _peer, stranger) = terminal_world();
        assert!(
            !term.is_command_authorized(&world, &Command::Transfer { target: stranger, amount: 1 }),
            "the terminal-cell does NOT reach the stranger"
        );
        let h0 = world.height();
        let r = term.run(&mut world, Command::Transfer { target: stranger, amount: 1 });
        assert!(
            matches!(r, Err(CommandError::OutOfMandate { .. })),
            "an out-of-mandate command must be REFUSED, got {r:?}"
        );
        // Fail-closed: nothing changed (no turn, no receipt) — but the REFUSAL is
        // recorded in the history (never faked away).
        assert_eq!(world.height(), h0, "a refused command commits no turn");
        assert_eq!(world.receipts().len(), 0, "a refused command appends no receipt");
        assert_eq!(term.history().len(), 1, "the refusal is recorded");
        assert!(!term.history()[0].committed, "shown as REFUSED");
        assert!(term.history()[0].result.contains("REFUSED"));
    }

    #[test]
    fn an_authorized_but_overspending_command_is_rejected_by_the_executor() {
        // The two gates compose: a command that PASSES the cap-gate (in-mandate)
        // can still be REJECTED by the EXECUTOR gate (e.g. overspending). It is
        // shown as REFUSED with the executor's reason, distinct from out-of-mandate.
        let (mut world, mut term, peer, _stranger) = terminal_world();
        // Transfer MORE than the terminal-cell holds (10_000) → executor rejects.
        let r = term.run(&mut world, Command::Transfer { target: peer, amount: 1_000_000 });
        assert!(
            matches!(r, Err(CommandError::ExecutorRejected(_))),
            "an overspend passes the cap-gate but the executor rejects it, got {r:?}"
        );
        assert_eq!(world.height(), 0, "nothing committed");
        assert!(!term.history()[0].committed);
    }

    // ── THE VIEW: the panel model reflects the terminal's real authority + output ──

    #[test]
    fn the_view_reflects_the_mandate_and_the_committed_output() {
        let (mut world, mut term, peer, stranger) = terminal_world();
        // Run one in-mandate command (commits) + one out-of-mandate (refused).
        term.run(&mut world, Command::Transfer { target: peer, amount: 100 }).unwrap();
        let _ = term.run(&mut world, Command::Transfer { target: stranger, amount: 1 });

        let v = TerminalView::build(&term, &world);
        assert!(v.backed, "the terminal cell is live");
        // The mandate badge includes the peer (reachable) + the backing cell.
        assert!(
            v.reachable_short.contains(&crate::reflect::short_hex(peer.as_bytes())),
            "the peer is in the terminal's reachable mandate"
        );
        assert!(
            !v.reachable_short.contains(&crate::reflect::short_hex(stranger.as_bytes())),
            "the stranger is NOT in the mandate"
        );
        assert_eq!(v.committed_count, 1, "one command committed");
        assert_eq!(v.lines.len(), 2, "both the commit and the refusal are in the output");
        assert!(v.lines[0].committed && !v.lines[1].committed);
    }

    #[test]
    fn a_terminal_over_a_missing_cell_is_unbacked_and_refuses() {
        let mut world = World::new();
        let ghost = CellId::from_bytes([0x88; 32]); // never installed
        let mut shell = Shell::new();
        let cap = shell.open_cell_view(ghost, "ghost-term");
        let mut term = TerminalCell::new(cap.surface(), ghost, "ghost-term");
        let v = TerminalView::build(&term, &world);
        assert!(!v.backed, "a missing backing cell is unbacked");
        let r = term.run(&mut world, Command::Emit { target: ghost, topic: "hi".into() });
        assert!(matches!(r, Err(CommandError::Unbacked)), "a dangling terminal refuses, got {r:?}");
    }
}
