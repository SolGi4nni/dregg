//! # `dreggnet-grain` — OFFERING #2: a confined GRAIN session as an [`Offering`].
//!
//! The dungeon (`dreggnet_offerings::dungeon`) is offering #0 — a confined,
//! verifiable, paid, per-session thing on the real dregg substrate. This crate is
//! offering #2: the confined thing is a **grain** — a Sandstorm-style sandboxed app
//! running as a cap-gated *grain turn-cell* on the dregg substrate.
//!
//! ## What a grain is here, and where the sandbox is REAL
//!
//! A grain is a worker cell admitted through the REAL `grain-turn` R2 minter
//! ([`grain_turn::ToolGatewayMinter`], "THE REAL `GrainTurnMinter`"). At [`open`] the
//! executor admits the grain worker under a `ToolGrant { rate_limit: budget, .. }` —
//! the grain is **confined to exactly `budget` metered turns** under one allowlisted
//! tool id. Each [`advance`](GrainOffering::advance) drives ONE real
//! `dregg_sdk::ToolGateway::invoke` executor turn on that worker cell
//! ([`grain_turn::ToolGatewayMinter::mint_turn`]) — a genuine committed kernel
//! transition whose `turn_hash` enters the executor's committed-turn manifest, and
//! whose state witnesses the action commit ([`grain_turn::action_commit`]), the
//! consumed total, and the heap root.
//!
//! **The confinement is the executor's own caveat, not prose.** The grant installs
//! `delegAdmit`'s RATE leg (`calls_made ≤ rate_limit`) plus the cell-program
//! `FieldLte`/`Monotonic` backstop on the `calls_made` counter. When the grain has
//! spent its whole grant, the next `mint_turn` → `ToolGateway::invoke` →
//! `deleg_admit` fails the RATE leg and the **executor refuses the turn host-side** —
//! nothing commits, no receipt. Every [`advance`](GrainOffering::advance) routes
//! through the real executor, so an over-cap move is an [`Outcome::Refused`] carrying
//! the *executor's own* refusal string. **The grain cannot act beyond its granted
//! sandbox** — the jailer is the kernel. The refusal is non-vacuous: the identical
//! action lands under a larger grant (a bigger `budget`), so the refusal tracks the
//! real cap, not a hardcoded reject (see `tests/driven.rs`).
//!
//! ## The six-method shape (the same one the dungeon proves end-to-end)
//!
//! - [`open`](GrainOffering::open) — admit a fresh confined grain worker under a
//!   rate-`budget` grant (the real `ToolGatewayMinter::open`).
//! - [`actions`](GrainOffering::actions) — the one in-confinement affordance
//!   ([`TURN_ACT`]), `enabled` iff the grain still has grant left (a cap-tooth
//!   decoration; the executor is the sole referee).
//! - [`advance`](GrainOffering::advance) — drive ONE real cap-bounded grain turn:
//!   [`Outcome::Landed`] (a committed kernel turn) for an in-cap action,
//!   [`Outcome::Refused`] (the executor's over-cap refusal) for a confinement
//!   violation.
//! - [`verify`](GrainOffering::verify) — re-witness the grain's committed turn chain
//!   against the executor's manifest + the on-ledger `calls_made` counter + the
//!   on-ledger action commit (reads REAL committed kernel state, not a mirror).
//! - [`render`](GrainOffering::render) — the grain's state + affordances as a deos
//!   [`Surface`].
//! - [`price`](GrainOffering::price) — the run cost of the grain's confined compute
//!   overlay (the substrate turn itself is always free + verifiable).
//!
//! ## Honest scope — which grain, and what a fuller grain offering adds
//!
//! This hosts the **minimal real grain-turn slice**: the `grain-turn` R2 minter's
//! cap-gated worker cell, driven directly. It is a *real* confined grain (a genuine
//! admitted `dregg_cell::Cell` under a genuine executor-enforced grant), not a demo
//! `.spk` app. A **fuller grain offering** composes more of the infra this slice
//! deliberately leaves out:
//! - a real packaged grain (`sandstorm-bridge`'s signed `.spk` + `dga1_` powerbox
//!   cap rail; `grain-commons`' hatchery/fork/publish) so the grain is a *shareable,
//!   pedigreed app*, not an anonymous worker cell;
//! - the OS-jailed body (`grain-jail`'s `real-jail`: macOS Seatbelt / Linux
//!   seccomp+Landlock) so a *subprocess* brain is confined, not only the cap grant;
//! - the durable lease + settlement rail (`hosted-lease` / `hosted-durable`) so the
//!   grain survives restarts and its metered turns settle as conserved value;
//! - the R1 renter anchor + R3 whole-history STARK leg (`grain-verify`:
//!   `GrainAttestation`, `r3_verify`) so `verify` becomes tamper-evidence →
//!   unfoolability, folding each turn's rotated EffectVM leg (grain-verify's
//!   `WHOLE_HISTORY_GAP`).
//!
//! What is REAL here vs stubbed: the confined grain worker cell, the executor-driven
//! grain turn, and the over-cap refusal are REAL (kernel-enforced). The
//! `Outcome::Landed` [`TurnReceipt`] is a faithful **view** whose load-bearing field
//! — `turn_hash` — is the genuine committed turn hash from the executor's manifest;
//! the heap-root witness fed to each turn is session-derived (in a fuller offering it
//! is the agent's real committed cell root).

use deos_view::{MenuItem, ViewNode};
use dregg_agent::agent::GrainTurnMinter;
use dregg_app_framework::TurnReceipt;
use grain_turn::{action_commit, ToolGatewayMinter, ACTION_SLOT};

use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

/// The one in-confinement affordance verb every grain move fires — a single metered
/// grain action (one `ToolGateway::invoke` turn on the grain worker cell). The
/// action's `arg` is the action's cost (its draw against the grain's grant); `0` or
/// negative is normalised to a unit cost.
pub const TURN_ACT: &str = "act";

/// A committed grain turn this session landed — the genuine executor `turn_hash`
/// plus the action it was minted for. [`GrainOffering::verify`] re-witnesses each
/// against the executor's committed-turn manifest and the on-ledger action commit.
#[derive(Clone, Debug)]
struct LandedTurn {
    /// The genuine committed turn hash (the R2 link into the executor's manifest).
    turn_hash: [u8; 32],
    /// The action label this turn was minted for (witnessed as `action_commit`).
    label: String,
    /// The cost this action drew (witnessed as `action_commit`).
    cost: i64,
}

/// **A confined grain session over the REAL substrate** — the live grain turn-cell.
/// Owns the real `grain-turn` R2 minter (the cap-gated worker cell + its
/// executor-enforced `calls_made` grant), the granted cap `budget`, the running
/// consumed total (witnessed on each turn), and the landed-turn log (each a genuine
/// committed kernel turn) [`GrainOffering::verify`] re-witnesses.
pub struct GrainSession {
    /// The REAL confined grain: a cap-gated worker cell admitted under a rate-`budget`
    /// grant. Every grain turn is a genuine `ToolGateway::invoke` on this cell; the
    /// executor's `calls_made` caveat refuses an over-cap turn host-side.
    minter: ToolGatewayMinter,
    /// The granted cap — the number of metered turns the grain may commit. The
    /// executor's RATE leg (`calls_made ≤ budget`) is the sandbox boundary.
    budget: i64,
    /// The running consumed total (Σ costs of landed turns), witnessed at each turn's
    /// `CONSUMED_SLOT`. A session meter mirror beside the kernel's `calls_made`.
    consumed: i64,
    /// The grain's confinement domain (its session identity; the mint token domain).
    domain: String,
    /// The committed grain turns, in order — each a genuine landed kernel turn.
    landed: Vec<LandedTurn>,
}

impl GrainSession {
    /// The grain's confinement domain (its session identity).
    pub fn domain(&self) -> &str {
        &self.domain
    }

    /// The granted cap — how many metered turns the grain may commit before the
    /// executor refuses (the sandbox boundary).
    pub fn budget(&self) -> i64 {
        self.budget
    }

    /// The number of grain turns committed so far — read off the REAL ledger (the
    /// executor's own `calls_made` counter, not a mirror).
    pub fn calls_made(&self) -> i64 {
        self.minter.calls_made()
    }

    /// The grant the grain has left (`budget − calls_made`, floored at 0) — its
    /// un-exercised sandbox authority.
    pub fn headroom(&self) -> i64 {
        (self.budget - self.calls_made()).max(0)
    }

    /// Whether the grain has spent its whole grant (any further action is refused).
    pub fn is_exhausted(&self) -> bool {
        self.calls_made() >= self.budget
    }

    /// The number of real verified grain turns landed so far.
    pub fn receipts_len(&self) -> usize {
        self.landed.len()
    }

    /// The running consumed total (Σ costs), witnessed on the committed turns.
    pub fn consumed(&self) -> i64 {
        self.consumed
    }

    /// A compact one-line projection of the grain's confined state (for the surface).
    pub fn state_line(&self) -> String {
        format!(
            "grain {} · turns {}/{} · consumed {} · headroom {} caps{}",
            self.domain,
            self.calls_made(),
            self.budget,
            self.consumed,
            self.headroom(),
            if self.is_exhausted() {
                " · SANDBOX SPENT"
            } else {
                ""
            },
        )
    }
}

/// **The grain offering** — offering #2. A stateless factory over confined grain
/// sessions; each [`open`](Offering::open) admits a fresh cap-gated grain worker cell
/// under a rate-`budget` grant. Carries the per-move [`RunCost`] (the free tier by
/// default; a paid tier prices the grain's confined compute overlay).
pub struct GrainOffering {
    /// The cap every opened grain is confined to — the number of metered turns the
    /// executor's `calls_made` grant admits before refusing.
    budget: i64,
    /// Run-credits a grain action's confined compute costs (`0` → free tier). The
    /// substrate turn itself is always free + verifiable; this prices the overlay.
    run_credits: u64,
}

impl GrainOffering {
    /// A free-tier grain offering confining each session to `budget` metered turns.
    pub fn new(budget: i64) -> Self {
        GrainOffering {
            budget: budget.max(0),
            run_credits: 0,
        }
    }

    /// A paid-tier grain offering: each action's confined compute costs `credits`
    /// run-credits (the frontend debits them; the substrate turn stays free).
    pub fn paid(budget: i64, credits: u64) -> Self {
        GrainOffering {
            budget: budget.max(0),
            run_credits: credits,
        }
    }

    /// The grain's single in-confinement affordance — one metered grain action,
    /// `enabled` iff the grain still has grant left. `enabled` is the cap tooth SHOWN
    /// (a dimmed row once the sandbox is spent), a decoration only: the executor is
    /// the sole referee — firing it anyway lands a real over-cap [`Outcome::Refused`].
    fn grain_actions(&self, session: &GrainSession) -> Vec<Action> {
        vec![Action::new(
            "Take one confined grain action",
            TURN_ACT,
            1,
            !session.is_exhausted(),
        )]
    }
}

/// The session-derived heap-root witness fed to each grain turn's `HEAP_ROOT_SLOT`.
/// In a fuller grain offering this is the grain body's real committed cell root; here
/// it is a deterministic session witness `BLAKE3(domain ‖ turn_index)` — a real
/// committed field on the turn, just not (yet) an agent heap.
fn heap_witness(domain: &str, turn_index: usize) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(domain.as_bytes());
    h.update(&(turn_index as u64).to_le_bytes());
    *h.finalize().as_bytes()
}

impl Offering for GrainOffering {
    type Session = GrainSession;

    /// Admit a fresh confined grain worker cell under a rate-`budget` grant (the real
    /// [`ToolGatewayMinter::open`]). The `seed` in `cfg` names the confinement domain
    /// (the grain's session identity). Fails only if the executor refuses to admit
    /// the grain worker → [`OfferingError::Deploy`].
    fn open(&self, cfg: SessionConfig) -> Result<GrainSession, OfferingError> {
        let domain = format!("dreggnet-grain-{}", cfg.seed.unwrap_or(1));
        let minter = ToolGatewayMinter::open(&domain, self.budget)
            .map_err(|e: dregg_sdk::SdkError| OfferingError::Deploy(e.to_string()))?;
        Ok(GrainSession {
            minter,
            budget: self.budget,
            consumed: 0,
            domain,
            landed: Vec::new(),
        })
    }

    fn actions(&self, session: &GrainSession) -> Vec<Action> {
        self.grain_actions(session)
    }

    /// **Drive ONE real cap-bounded grain turn.** Routes the action through the real
    /// executor ([`ToolGatewayMinter::mint_turn`] → `ToolGateway::invoke`): a legal,
    /// in-cap action commits a genuine kernel turn ([`Outcome::Landed`], its
    /// `turn_hash` entering the executor's manifest); an action past the grain's
    /// grant is the **executor's own** over-cap refusal ([`Outcome::Refused`]) —
    /// nothing commits, no landed turn recorded (the confinement tooth). `actor` is
    /// session-level attribution (the world-signed turn is the executor's).
    fn advance(&self, session: &mut GrainSession, input: Action, _actor: DreggIdentity) -> Outcome {
        if input.turn != TURN_ACT {
            return Outcome::Refused(format!("unknown grain affordance: {}", input.turn));
        }
        let cost = if input.arg > 0 { input.arg } else { 1 };
        let label = if input.label.is_empty() {
            TURN_ACT.to_string()
        } else {
            input.label.clone()
        };
        let turn_index = session.landed.len();
        let consumed_after = session.consumed + cost;
        let cell_root = heap_witness(&session.domain, turn_index);

        // THE REAL EXECUTOR TURN. `Ok` = a genuine committed kernel turn on the grain
        // worker cell. `Err` = the executor REFUSED host-side (the `calls_made` RATE
        // caveat: the grain has spent its granted cap) — a confinement violation the
        // kernel, not this code, rejected.
        match session
            .minter
            .mint_turn(&label, cost, consumed_after, cell_root)
        {
            Ok(turn_hash) => {
                session.landed.push(LandedTurn {
                    turn_hash,
                    label,
                    cost,
                });
                session.consumed = consumed_after;
                // A `TurnReceipt` VIEW whose load-bearing, non-forgeable field is the
                // genuine committed `turn_hash` (the executor's manifest entry); the
                // agent/action_count fields come from the real committed grain cell.
                let receipt = TurnReceipt {
                    turn_hash,
                    agent: session.minter.grain_cell(),
                    action_count: 1,
                    timestamp: turn_index as i64,
                    ..Default::default()
                };
                let ended = session.is_exhausted();
                Outcome::Landed { receipt, ended }
            }
            // The executor's OWN refusal string (over-cap / scope / deadline). The
            // grain cannot escape its sandbox: the kernel is the jailer.
            Err(reason) => Outcome::Refused(reason),
        }
    }

    /// **Re-witness the grain's committed turn chain against REAL kernel state.** Not
    /// a mirror: checks (1) the executor's committed-turn manifest matches the landed
    /// turns exactly and in order; (2) the on-ledger `calls_made` counter equals the
    /// number of landed turns (the kernel's own count of committed grain turns); (3)
    /// the on-ledger action commit ([`ACTION_SLOT`]) equals the last action's
    /// [`action_commit`] (the last committed turn witnessed exactly the last action).
    /// A forged/reordered landed record breaks (1); a fabricated turn count breaks (2).
    fn verify(&self, session: &GrainSession) -> VerifyReport {
        let turns = session.landed.len();

        // (1) Every landed turn is a genuine committed turn, in order.
        let committed = session.minter.committed_turns();
        if committed.len() != turns {
            return VerifyReport::broken(
                turns,
                format!(
                    "committed-turn manifest has {} turns but {} landed",
                    committed.len(),
                    turns
                ),
            );
        }
        for (i, lt) in session.landed.iter().enumerate() {
            if committed[i] != lt.turn_hash {
                return VerifyReport::broken(
                    turns,
                    format!(
                        "landed turn {i} is not the executor's committed turn (forged/reordered)"
                    ),
                );
            }
        }

        // (2) The kernel's own committed counter equals the number of landed turns.
        let on_ledger = session.minter.calls_made();
        if on_ledger != turns as i64 {
            return VerifyReport::broken(
                turns,
                format!("on-ledger calls_made {on_ledger} != {turns} landed turns"),
            );
        }

        // (3) The last committed turn witnessed exactly the last action.
        if let Some(last) = session.landed.last() {
            let expect = action_commit(&last.label, last.cost);
            match session.minter.read_slot(ACTION_SLOT) {
                Some(on) if on == expect => {}
                Some(_) => {
                    return VerifyReport::broken(
                        turns,
                        "on-ledger action commit != the last landed action (tampered)".to_string(),
                    );
                }
                None => {
                    return VerifyReport::broken(
                        turns,
                        "grain turn-cell absent from the ledger".to_string(),
                    );
                }
            }
        }

        VerifyReport::ok(turns)
    }

    /// Render the grain's confined state as a deos [`Surface`]: the state line
    /// (turns/cap/consumed/headroom), the verified-turn count, and the one
    /// in-confinement affordance as a cap-gated [`Menu`] (a dimmed `!enabled` row once
    /// the sandbox grant is spent — the cap tooth shown, not hidden).
    fn render(&self, session: &GrainSession) -> Surface {
        let actions = self.grain_actions(session);

        // THE DIRECTIVE, first — every plaque here was `muted`/`genuine`, so the page opened on a
        // state line (`turns 0/1000 · consumed 0 · headroom …`) and never said what to press. The
        // shared web skin promotes the leading paragraph of an `accent` plaque to the page's lead.
        let directive = if session.is_exhausted() {
            format!(
                "This grain has spent its whole grant — all {} metered turn(s) are gone, and a \
                 further request is refused by the executor's own `calls_made` caveat rather than \
                 by this page. Open a fresh grain to meter more work.",
                session.budget
            )
        } else {
            format!(
                "Press a request below to spend ONE metered turn of this grain's grant: {} of {} \
                 remain. The cap rides in the committed turn, so an over-cap press is refused \
                 host-side instead of quietly dropped.",
                session.headroom(),
                session.budget
            )
        };
        let mut children = vec![
            ViewNode::Section {
                title: "Your next move".to_string(),
                tag: "accent".to_string(),
                children: vec![ViewNode::Text(directive)],
            },
            ViewNode::Section {
                title: "Grain".to_string(),
                tag: "muted".to_string(),
                children: vec![ViewNode::Text(session.state_line())],
            },
            ViewNode::Section {
                title: "Confinement".to_string(),
                tag: "muted".to_string(),
                children: vec![ViewNode::Text(format!(
                    "cap-gated to {} metered turn(s); the executor's calls_made caveat refuses an over-cap turn host-side",
                    session.budget
                ))],
            },
            ViewNode::Section {
                title: "Verified turns".to_string(),
                tag: "genuine".to_string(),
                children: vec![ViewNode::Text(session.receipts_len().to_string())],
            },
        ];

        if session.is_exhausted() {
            children.push(ViewNode::Section {
                title: "Sandbox grant spent".to_string(),
                tag: "genuine".to_string(),
                children: vec![ViewNode::Text(
                    "the grain has committed its whole grant; a further action is refused by the executor".to_string(),
                )],
            });
        }

        let items = actions
            .iter()
            .map(|a| MenuItem {
                label: a.label.clone(),
                turn: a.turn.clone(),
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect();
        children.push(ViewNode::Section {
            title: "The grain's move".to_string(),
            tag: "accent".to_string(),
            children: vec![ViewNode::Menu { items }],
        });

        Surface(ViewNode::Section {
            title: format!("Confined grain — {}", session.domain),
            tag: "accent".to_string(),
            children,
        })
    }

    /// The move's [`RunCost`] — the free tier by default; the paid tier prices the
    /// grain's confined compute overlay (the substrate turn itself is always free).
    fn price(&self, _input: &Action) -> RunCost {
        RunCost::credits(self.run_credits)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The tamper tooth — an in-crate test reaching the session's private `landed`
// log to forge the committed record. The end-to-end driven flow (open → advance →
// confinement-refused → verify → render) lives in `tests/driven.rs`.
// ─────────────────────────────────────────────────────────────────────────────
#[cfg(test)]
mod forge_tests {
    use super::*;

    /// A legal grain line re-verifies; then a FORGED landed record (the first turn's
    /// hash swapped) fails verify — it no longer matches the executor's committed-turn
    /// manifest. The real committed-turn tooth, through the [`Offering`] API.
    #[test]
    fn a_forged_turn_hash_fails_verify() {
        let off = GrainOffering::new(3);
        let mut s = off.open(SessionConfig::with_seed(7)).expect("grain admits");
        let actor = DreggIdentity("renter".to_string());

        assert!(off
            .advance(&mut s, Action::new("act", TURN_ACT, 1, true), actor.clone())
            .landed());
        assert!(off
            .advance(&mut s, Action::new("act", TURN_ACT, 1, true), actor)
            .landed());
        assert!(off.verify(&s).verified, "the legal grain line re-verifies");

        // Forge the recorded chain: swap the first landed turn hash; the committed
        // manifest no longer matches → verify breaks.
        s.landed[0].turn_hash = [0xabu8; 32];
        let report = off.verify(&s);
        assert!(!report.verified, "a forged turn hash must fail verify");
    }
}
