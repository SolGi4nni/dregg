//! THE SWARM COORDINATOR — multi-agent activity surface (A2, the ADOS keystone).
//!
//! **ADOS north-star:** an agent is an intricate LOOP; dregg grounds the ONE
//! seam that matters — **the agent's ACTIONS, at the tool-call/turn boundary**.
//! A2 extends A1 (single agent-activity surface) to N agents coordinating in a
//! swarm: each member is a cap-confined `Surface` cell; their actions are
//! cap-gated, receipted turns; and their COORDINATION is routed through the
//! **notify edge** — an `EmitEvent` turn committed by one member that deposits
//! a pending wake in the recipient's inbox, to be DRAINED by the recipient in
//! its OWN SEPARATE FUTURE TURN (async, not synchronous, not a joint turn).
//!
//! # The notify-edge model
//!
//! ```text
//!   member A  ──(EmitEvent turn · receipt rA)──▶  notify inbox of B
//!                                                         │
//!                                                  [pending wake]
//!                                                         │
//!   member B  ◀──(drain turn · receipt rB)─────────────────
//! ```
//!
//! The two receipts (`rA`, `rB`) are INDEPENDENT on-ledger records — they share
//! no parent, no synchrony, no joint authorization. The wake is observable (the
//! `NotifyEdge` appears in the inbox) but the drain is entirely B's next turn:
//! B decides when to drain, how, and with what effects. This is the ocap async-
//! message model applied to a swarm: the coordinator sees the causality (A→B)
//! without forcing any synchronization (the "pale-ghost" question for agents:
//! *can an operator be fooled about what two agents coordinated?* No — the
//! `EventEmitted` in the dynamics and the drain receipt are the on-ledger truth).
//!
//! # Two coordination shapes (async edge + atomic bundle) and the SURFACE
//!
//! The swarm offers TWO coordination primitives, plus a cap-confined pane per
//! member:
//!
//!   * **The async notify edge** ([`Swarm::run`] → [`Swarm::drain_notify`]) —
//!     causal-but-independent, above (A wakes B; B drains in its OWN future turn).
//!   * **The atomic swarm turn** ([`Swarm::run_atomic`]) — N member-actions
//!     bundled into ONE forest turn the executor commits ALL-OR-NOTHING (a
//!     coordinator atomically settling a multi-party exchange or fanning a batch
//!     out in one verified step; bounded by the coordinator's mandate, ONE
//!     receipt for the whole bundle). Where the notify edge deliberately does NOT
//!     synchronize, the atomic turn deliberately DOES — both are real, and they
//!     compose (a bundled `EmitEvent` still deposits a notify edge).
//!   * **The per-member SURFACE** ([`Swarm::bind_surface`]) — each member bound
//!     to a cap-confined shell surface (its pane), owned via a REAL
//!     `dregg_firmament` [`SurfaceCapability`](crate::surface::SurfaceCapability)
//!     the shell gates every window op on. So the swarm's panes carry the SAME
//!     no-ambient-authority discipline at the glass as its turns do on the
//!     ledger (`docs/DREGG-DESKTOP-OS.md`: each agent pane is a confined Surface
//!     the shell composites).
//!
//! # What is runnable
//!
//! This module is gpui-FREE and `cargo test`-able. The cockpit maps
//! [`SwarmView`] onto a new `SWARM` tab, backed by real turns through the
//! embedded [`World`](crate::world::World). The demo path:
//!   1. `Swarm::new(world, members)` — seed N agent cells with mandates.
//!   2. `Swarm::run_member(world, agent, cmd)` — a member commits an
//!      in-mandate command (cap-gated turn); if it includes an `EmitEvent`
//!      targeting another member, a `NotifyEdge` lands in that member's inbox.
//!   3. `Swarm::drain_notify(world, agent)` — the target member commits a drain
//!      (its own separate ack turn); the inbox entry is consumed.
//!   4. `SwarmView::build(swarm, world)` — the gpui-free render model for the
//!      SWARM tab (each member's mandate + action count + inbox drain state).
//!
//! # SDK binding
//!
//! The `NotifyEdge` + `SwarmInbox` model binds to the real dregg SDK at:
//!   - `dregg_turn::action::Effect::EmitEvent` — the sender's receipted turn
//!     (already in the executor; no new protocol verbs needed).
//!   - `dregg_cell::Cell::capabilities` — the mandate (`SwarmMember::mandate`
//!     reads from the live cell's c-list, same as `AgentActivity`).
//!   - `dregg_sdk::embed::DreggEngine::execute_turn` — the swarm's turns route
//!     through the same verified executor, no special path.
//! The inbox is LOCAL STATE here (starbridge-v2 tracks it from the dynamics
//! stream); in a distributed setting it would be the recipient cell's own state
//! field (a pending-event queue in the cell's storage), with the dregg-node
//! routing `EmitEvent` as a network message and the cell's program draining it.

use std::collections::HashMap;

use dregg_cell::CellId;

use crate::dynamics::WorldEvent;
use crate::world::{self, CommitOutcome, World};

/// One pending notification in a swarm member's inbox: a wake signal deposited
/// by a COMMITTED `EmitEvent` turn from another member. The recipient drains it
/// in its OWN separate future turn — the async notify edge, not a joint turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotifyEdge {
    /// The swarm member whose committed turn deposited this notification.
    pub from: CellId,
    /// The world height at which the sender's `EmitEvent` turn committed.
    pub turn_height: u64,
    /// The receipt hash of the SENDER'S committed turn (the provenance link —
    /// not the drain; this is the seam record the operator can audit).
    pub sender_receipt: [u8; 32],
    /// The topic hash (Blake3 of the topic string, as the executor hashed it).
    pub topic_hash: [u8; 32],
    /// Data payload length (bytes) — informational, for the feed label.
    pub data_len: usize,
    /// Whether this notification has been drained (consumed by the recipient's
    /// own committed ack turn). A drained edge is shown in the history but is
    /// NOT actionable (the inbox drain is one-shot, fail-safe closed).
    pub drained: bool,
    /// The receipt hash of the DRAIN TURN (the recipient's own ack), if
    /// drained. Proves the recipient actually observed + acknowledged the wake.
    pub drain_receipt: Option<[u8; 32]>,
}

impl NotifyEdge {
    /// Whether this notification is pending (not yet drained).
    pub fn is_pending(&self) -> bool {
        !self.drained
    }

    /// A short human label for the swarm activity feed.
    pub fn label(&self) -> String {
        let short_from = crate::reflect::short_hex(self.from.as_bytes());
        let topic_short = hex::encode(&self.topic_hash[..4]);
        if self.drained {
            format!(
                "notify from {short_from} topic 0x{topic_short}… — DRAINED (receipt {})",
                self.drain_receipt
                    .map(|h| crate::reflect::short_hex(&h))
                    .unwrap_or_default()
            )
        } else {
            format!("notify from {short_from} topic 0x{topic_short}… — PENDING wake")
        }
    }
}

/// THE PER-MEMBER BUDGET METER — the conserved-spend face of the swarm (N1 /
/// `docs/ADOS-DEEPENING.md` §3.3, `docs/AGENT-SWARM-UX.md` §5).
///
/// `spent` is the RUNNING SUM of the metered computrons across every committed
/// action the member took through [`Swarm::run`] / [`Swarm::run_atomic`] /
/// [`Swarm::drain_notify`] — the same `computrons` already carried on each
/// [`SwarmActionOutcome`], not a re-derived estimate. `ceiling` is an OPTIONAL
/// metered-computron cap: when set, [`Swarm::run`] REFUSES a dispatch that would
/// push `spent` past it BEFORE the turn runs (fail-closed — the
/// [`SwarmError::BudgetExhausted`] guarantee firing at the seam, the swarm-layer
/// twin of the conservation refusal).
///
/// This is the FLOOR model (a plain conserved counter the swarm owns). The depth
/// lift to a real `dregg_coord::StingrayCounter` shared budget (so "the swarm
/// spent at most B" is *provable* across N members) is the named N9 weld; the
/// floor here is exact for the single-image swarm.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BudgetMeter {
    /// The running sum of metered computrons this member has spent on committed
    /// actions (monotonically non-decreasing; a refused action spends nothing).
    pub spent: u64,
    /// An optional metered-computron ceiling. `None` = unbounded (no budget gate);
    /// `Some(c)` = [`Swarm::run`] refuses a dispatch whose post-spend would exceed
    /// `c` (fail-closed, before the turn runs).
    pub ceiling: Option<u64>,
}

impl BudgetMeter {
    /// The headroom remaining under the ceiling (`ceiling - spent`, saturating at
    /// 0), or `None` if the member is unbounded.
    pub fn headroom(&self) -> Option<u64> {
        self.ceiling.map(|c| c.saturating_sub(self.spent))
    }

    /// Whether spending `cost` more computrons would BREACH the ceiling (strictly
    /// exceed it). An unbounded meter never breaches. A `cost` that lands the
    /// member EXACTLY on the ceiling is admitted (the ceiling is the inclusive
    /// bound the member may reach but not pass).
    pub fn would_breach(&self, cost: u64) -> bool {
        match self.ceiling {
            Some(c) => self.spent.saturating_add(cost) > c,
            None => false,
        }
    }

    /// Whether the member is at or over its ceiling already (no further bounded
    /// spend is possible) — the "amber → red" boundary the panel colors.
    pub fn is_exhausted(&self) -> bool {
        match self.ceiling {
            Some(c) => self.spent >= c,
            None => false,
        }
    }
}

/// THE SWARM-AGGREGATE BUDGET — the conserved-spend strip across all members
/// (`docs/AGENT-SWARM-UX.md` §4.5). `total_spent` is the sum of every member's
/// metered spend; `total_ceiling` is the sum of the SET ceilings (members with no
/// ceiling contribute nothing to it — `bounded_members` counts how many are
/// gated); `headroom` is `total_ceiling - total_spent` saturating at 0.
///
/// The aggregate is the answer to "could this swarm have cost more than I
/// allowed?" — over the bounded members it is a hard, conserved bound (the floor
/// model; the N9 Stingray weld makes it a single shared pool).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SwarmBudget {
    /// The sum of metered computrons spent across ALL members.
    pub total_spent: u64,
    /// The sum of the SET ceilings (unbounded members contribute nothing).
    pub total_ceiling: u64,
    /// `total_ceiling - total_spent`, saturating at 0 (headroom over the bounded
    /// members; meaningful only against `bounded_members`).
    pub headroom: u64,
    /// How many members carry a ceiling (the bounded subset the aggregate bounds).
    pub bounded_members: usize,
}

/// One member of a swarm — an agent cell with a mandate, a surface binding, and
/// an inbox of pending notifications from peers. Each member is a cap-confined
/// `Surface` cell: its actions are cap-gated by its mandate (same as
/// `AgentActivity`), and its inbox is populated by peers' `EmitEvent` turns.
#[derive(Clone, Debug)]
pub struct SwarmMember {
    /// The agent cell this member IS.
    pub agent: CellId,
    /// A short operator-legible id (abbreviated cell id).
    pub short: String,
    /// The name the operator assigned this member at boot.
    pub name: String,
    /// The `SurfaceId` this member renders into (its window handle in the shell).
    /// `None` if the swarm was constructed without a shell (headless / test).
    pub surface: Option<crate::surface::SurfaceId>,
    /// THE PER-MEMBER SURFACE CAPABILITY — the REAL `dregg_firmament` cap that
    /// confines this member's pane (`docs/DREGG-DESKTOP-OS.md`: each agent pane is
    /// a cap-confined Surface the shell composites). Held once the member is
    /// bound to a shell surface via [`Swarm::bind_surface`]; the shell gates every
    /// window op on it (a forged cap is refused on every op), so a swarm member's
    /// pane is exactly as authorized as the cap it holds — nothing ambient. `None`
    /// until bound (headless swarms run without a shell).
    pub surface_cap: Option<crate::surface::SurfaceCapability>,
    /// The inbox: pending (and drained) notifications from peer members.
    /// Newest-first so the panel shows the most recent at the top.
    pub inbox: Vec<NotifyEdge>,
    /// The committed action count from the world's receipt log (the member's
    /// grounded step counter — filled in by `SwarmView::build`, or
    /// `Swarm::member_action_count`).
    pub action_count: usize,
    /// Whether the backing cell is present in the live ledger.
    pub backed: bool,
    /// The member's live balance (resources its loop holds).
    pub balance: i64,
    /// THE BUDGET METER — the running metered-computron spend + an optional
    /// ceiling. [`Swarm::run`] refuses a dispatch that would breach the ceiling
    /// BEFORE it runs (fail-closed). `spent` grows by each committed action's
    /// metered computrons.
    pub budget: BudgetMeter,
}

impl SwarmMember {
    fn new(agent: CellId, name: impl Into<String>) -> Self {
        let short = crate::reflect::short_hex(agent.as_bytes());
        SwarmMember {
            agent,
            short,
            name: name.into(),
            surface: None,
            surface_cap: None,
            inbox: Vec::new(),
            action_count: 0,
            backed: false,
            balance: 0,
            budget: BudgetMeter::default(),
        }
    }

    /// Whether this member is bound to a cap-confined shell surface (its pane).
    pub fn has_surface(&self) -> bool {
        self.surface_cap.is_some()
    }

    /// How many notifications are pending (undrained) in the inbox.
    pub fn pending_notify_count(&self) -> usize {
        self.inbox.iter().filter(|n| n.is_pending()).count()
    }
}

/// Why a swarm command was refused. Mirrors `CommandError` from terminal.rs but
/// with swarm-specific context (which member refused, etc.).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SwarmError {
    /// The acting member holds no capability reaching the command's target.
    OutOfMandate { member: CellId, target: CellId },
    /// The acting member's backing cell is gone from the ledger.
    Unbacked { member: CellId },
    /// The turn was rejected by the real executor (permission/balance/guarantee).
    ExecutorRejected { member: CellId, reason: String },
    /// No member with the given `CellId` exists in this swarm.
    UnknownMember { agent: CellId },
    /// THE BUDGET CEILING FIRING — the member has a metered-computron ceiling and
    /// this dispatch is refused BEFORE it runs (fail-closed, no turn committed) to
    /// keep its `spent` from breaching the `ceiling`. The swarm-layer answer to the
    /// runaway-spend fear: a provable bound on the metered cost, enforced AT the
    /// seam rather than reconciled after. `would_be` is the spend the dispatch
    /// would push the member to if it ran (the prospective sum). Note the bound is
    /// over COMPUTRONS, not dollars (`docs/ADOS-DEEPENING.md` §3.3 carries that gap).
    BudgetExhausted {
        member: CellId,
        spent: u64,
        ceiling: u64,
        would_be: u64,
    },
}

impl SwarmError {
    /// A short operator-legible label.
    pub fn label(&self) -> String {
        match self {
            SwarmError::OutOfMandate { member, target } => format!(
                "REFUSED — {} holds no cap reaching {} (out-of-mandate)",
                crate::reflect::short_hex(member.as_bytes()),
                crate::reflect::short_hex(target.as_bytes()),
            ),
            SwarmError::Unbacked { member } => format!(
                "REFUSED — member {} unbacked (cell gone from ledger)",
                crate::reflect::short_hex(member.as_bytes()),
            ),
            SwarmError::ExecutorRejected { member, reason } => format!(
                "REFUSED by executor — member {} : {reason}",
                crate::reflect::short_hex(member.as_bytes()),
            ),
            SwarmError::UnknownMember { agent } => format!(
                "REFUSED — no member {} in this swarm",
                crate::reflect::short_hex(agent.as_bytes()),
            ),
            SwarmError::BudgetExhausted {
                member,
                spent,
                ceiling,
                would_be,
            } => format!(
                "REFUSED — member {} budget exhausted (spent {spent} + this would reach {would_be} > ceiling {ceiling})",
                crate::reflect::short_hex(member.as_bytes()),
            ),
        }
    }
}

/// The outcome of a swarm action — what committed, what notify edges landed.
#[derive(Clone, Debug)]
pub struct SwarmActionOutcome {
    /// The member that ran the action.
    pub member: CellId,
    /// Whether the turn committed.
    pub committed: bool,
    /// The receipt hash (if committed).
    pub receipt_hash: Option<[u8; 32]>,
    /// The world height after commit (if committed).
    pub height: Option<u64>,
    /// The computrons metered by the executor (if committed).
    pub computrons: u64,
    /// Any `NotifyEdge`s that were deposited into peer inboxes as a result of
    /// this action's `EmitEvent` effects. One entry per recipient member that
    /// received a wake. (Only inter-member events; self-notifications are
    /// filtered out in `Swarm::run`.)
    pub notify_edges: Vec<(CellId, NotifyEdge)>,
    /// A human-meaningful summary of the action's effects.
    pub summary: String,
}

/// THE SWARM COORDINATOR — N agent cells coordinating as confined Surface cells,
/// with the notify-edge inbox threading async wakes between them.
///
/// The swarm owns the inbox state (a local extension of the dynamics stream) and
/// the member registry. Every action routes through the REAL embedded executor
/// ([`World::commit_turn`]); the notify-edge population is derived from the
/// committed turn's `EventEmitted` dynamics.
pub struct Swarm {
    /// The member registry (stable CellId → SwarmMember). Insertion order is
    /// preserved so the panel renders members in boot order.
    members: Vec<SwarmMember>,
    /// A quick lookup from CellId to member index (to avoid linear scans on
    /// every inbox deposit).
    index: HashMap<CellId, usize>,
    /// Append-only action log (most-recent-last). Feeds the activity feed.
    action_log: Vec<SwarmActionOutcome>,
}

impl Swarm {
    /// Boot a swarm over `members` (a list of `(cell, name)` pairs). The cells
    /// must already exist in `world` (genesis-installed or earlier turns).
    pub fn new(world: &World, members: impl IntoIterator<Item = (CellId, impl Into<String>)>) -> Self {
        let mut swarm = Swarm {
            members: Vec::new(),
            index: HashMap::new(),
            action_log: Vec::new(),
        };
        for (cell, name) in members {
            swarm.add_member(world, cell, name);
        }
        swarm
    }

    /// Add a member to the swarm (crate-visible so tests + cockpit can extend it
    /// after boot). Refreshes the member's live state from `world`.
    pub fn add_member(&mut self, world: &World, agent: CellId, name: impl Into<String>) {
        let idx = self.members.len();
        let mut m = SwarmMember::new(agent, name);
        m.backed = world.ledger().contains(&agent);
        if let Some(c) = world.ledger().get(&agent) {
            m.balance = c.state.balance();
        }
        m.action_count = world.receipts().iter().filter(|r| r.agent == agent).count();
        self.members.push(m);
        self.index.insert(agent, idx);
    }

    /// Whether the swarm contains a member with this `CellId`.
    pub fn has_member(&self, agent: &CellId) -> bool {
        self.index.contains_key(agent)
    }

    /// The number of members in the swarm.
    pub fn len(&self) -> usize {
        self.members.len()
    }

    /// Whether the swarm has no members.
    pub fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    /// The action log (most-recent-last) — the swarm's grounded seam history.
    pub fn action_log(&self) -> &[SwarmActionOutcome] {
        &self.action_log
    }

    /// Borrow the member list (boot order).
    pub fn members(&self) -> &[SwarmMember] {
        &self.members
    }

    /// **RUN A SWARM ACTION — the cap-gated, receipted, notify-edge-routing seam.**
    ///
    /// This is A2's one seam: every action the swarm takes routes here, is
    /// cap-gated, runs through the real executor, and (if it includes
    /// `EmitEvent` effects targeting OTHER members) deposits `NotifyEdge`s
    /// in those members' inboxes. The caller supplies a typed `SwarmCommand`
    /// (same vocabulary as `terminal::Command`) or the more powerful
    /// `raw_effects` path for multi-effect turns.
    ///
    /// Steps:
    ///   1. Resolve `agent` → member; fail if unknown.
    ///   2. Confirm the backing cell is live; fail with `Unbacked` otherwise.
    ///   3. **CAP-GATE** — confirm the acting cell holds authority reaching the
    ///      effect target (same `has_access` check as `TerminalCell::run`).
    ///   3b. **BUDGET GATE** — if the member has spent its metered-computron
    ///      ceiling, REFUSE here (fail-closed, before the executor runs — no turn
    ///      commits, no height advance; [`SwarmError::BudgetExhausted`]).
    ///   4. Run the turn through the REAL executor via `World::commit_turn`.
    ///   5. On commit, scan the turn's new `EventEmitted` dynamics for inter-
    ///      member events; deposit `NotifyEdge`s in the recipients' inboxes.
    ///   6. Update the acting member's `action_count` + `balance`; append the
    ///      `SwarmActionOutcome` to the log.
    ///
    /// Returns the outcome (committed or refused, with notify edges).
    pub fn run(
        &mut self,
        world: &mut World,
        agent: CellId,
        effects: Vec<dregg_turn::action::Effect>,
    ) -> Result<SwarmActionOutcome, SwarmError> {
        // (1) Resolve member.
        let Some(&idx) = self.index.get(&agent) else {
            return Err(SwarmError::UnknownMember { agent });
        };

        // (2) Confirm backed.
        if world.ledger().get(&agent).is_none() {
            return Err(SwarmError::Unbacked { member: agent });
        }

        // (3) CAP-GATE: for each effect, confirm the acting cell reaches the
        //     target. Self-targeting effects are always OK (a cell reaches itself).
        for effect in &effects {
            if let Some(target) = effect_target(effect) {
                if target != agent {
                    let has_cap = world
                        .ledger()
                        .get(&agent)
                        .map(|c| c.capabilities.has_access(&target))
                        .unwrap_or(false);
                    if !has_cap {
                        return Err(SwarmError::OutOfMandate { member: agent, target });
                    }
                }
            }
        }

        // (3b) BUDGET GATE — fail-closed BEFORE the turn runs. A member that has
        //      already spent its metered-computron ceiling cannot dispatch again:
        //      we refuse here, before `commit_turn`, so NO turn commits and the
        //      height does not advance (the swarm-layer twin of the conservation
        //      refusal — `docs/ADOS-DEEPENING.md` §3.3). The bound is on the
        //      executor's metered `computrons_used` (summed into `spent`), the
        //      genuine cost, not a re-derived estimate. (The ceiling is over
        //      COMPUTRONS, not dollars — §3.3 names that as the carried gap; the
        //      `dregg_coord::StingrayCounter` shared-pool lift is the named N9 weld.)
        if self.members[idx].budget.is_exhausted() {
            let b = self.members[idx].budget;
            let ceiling = b.ceiling.unwrap_or(0);
            let ao = SwarmActionOutcome {
                member: agent,
                committed: false,
                receipt_hash: None,
                height: None,
                computrons: 0,
                notify_edges: Vec::new(),
                summary: format!(
                    "BUDGET EXHAUSTED — spent {} ≥ ceiling {ceiling} (dispatch refused, no commit)",
                    b.spent
                ),
            };
            self.action_log.push(ao);
            return Err(SwarmError::BudgetExhausted {
                member: agent,
                spent: b.spent,
                ceiling,
                would_be: b.spent, // already at/over — no further bounded spend
            });
        }

        // (4) Run through the REAL executor.
        let dyn_cursor_before = world.dynamics().cursor();
        let turn = world.turn(agent, effects);
        let outcome = world.commit_turn(turn);

        match outcome {
            CommitOutcome::Committed { ref receipt, .. } => {
                let receipt_hash = receipt.receipt_hash();
                // The world height AFTER commit is the turn's commit height.
                // (TurnReceipt has no `turn_height` field; the world tracks it.)
                let height = world.height();
                let computrons = receipt.computrons_used;

                // (5) Scan the new dynamics for inter-member EventEmitted entries.
                let new_events = world.dynamics().since(dyn_cursor_before);
                let mut notify_edges: Vec<(CellId, NotifyEdge)> = Vec::new();

                for ev in new_events {
                    if let WorldEvent::EventEmitted {
                        sender,
                        cell: recipient,
                        topic_hash,
                        data_len,
                    } = ev
                    {
                        // Only route inter-member events (sender → a DIFFERENT member
                        // in the swarm). Self-notifications are valid protocol events
                        // but don't produce inbox entries (no point waking yourself).
                        if sender == recipient {
                            continue;
                        }
                        if !self.index.contains_key(recipient) {
                            continue; // not a swarm member — skip
                        }
                        let edge = NotifyEdge {
                            from: *sender,
                            turn_height: height,
                            sender_receipt: receipt_hash,
                            topic_hash: *topic_hash,
                            data_len: *data_len,
                            drained: false,
                            drain_receipt: None,
                        };
                        notify_edges.push((*recipient, edge));
                    }
                }

                // Deposit the edges into the recipients' inboxes (newest-first).
                for (recipient, edge) in &notify_edges {
                    if let Some(&ridx) = self.index.get(recipient) {
                        self.members[ridx].inbox.insert(0, edge.clone());
                    }
                }

                // Summarize the action's effects from the dynamics.
                let summary = summarize_events(new_events);

                // (6) Update acting member's counters + grow the budget meter by
                //     the metered computrons (the running conserved spend).
                let m = &mut self.members[idx];
                m.action_count += 1;
                m.budget.spent = m.budget.spent.saturating_add(computrons);
                if let Some(c) = world.ledger().get(&agent) {
                    m.balance = c.state.balance();
                }
                m.backed = true;

                let ao = SwarmActionOutcome {
                    member: agent,
                    committed: true,
                    receipt_hash: Some(receipt_hash),
                    height: Some(height),
                    computrons,
                    notify_edges: notify_edges.clone(),
                    summary,
                };
                self.action_log.push(ao.clone());
                Ok(ao)
            }
            CommitOutcome::Rejected { reason, .. } => {
                let ao = SwarmActionOutcome {
                    member: agent,
                    committed: false,
                    receipt_hash: None,
                    height: None,
                    computrons: 0,
                    notify_edges: Vec::new(),
                    summary: format!("REFUSED — {reason}"),
                };
                self.action_log.push(ao.clone());
                Err(SwarmError::ExecutorRejected { member: agent, reason })
            }
        }
    }

    /// **BIND A MEMBER TO A CAP-CONFINED SHELL SURFACE** — give a swarm member
    /// its own pane, owned via a REAL `dregg_firmament` `SurfaceCapability` the
    /// shell mints (`docs/DREGG-DESKTOP-OS.md`: each agent pane is a cap-confined
    /// Surface the shell composites). After binding, the member holds the cap
    /// that authorizes every window op on its pane — a forged cap is refused on
    /// every op (the ocap heart at the glass), so the swarm's panes carry the
    /// SAME no-ambient-authority discipline as its turns.
    ///
    /// The shell opens a cell-view surface over the member's agent cell (its pane
    /// renders the member's live cell state) and hands back the authorizing cap,
    /// which the member now holds. Returns the `SurfaceId` of the new pane, or a
    /// `SwarmError::UnknownMember` if the agent is not a member.
    ///
    /// The cockpit composites the bound panes through `Shell::compose`, so each
    /// swarm member becomes a real cap-confined window over the live world — the
    /// SURFACE realization of the swarm (every pane a confined surface the shell
    /// composites), beside the in-process notify-edge coordination.
    pub fn bind_surface(
        &mut self,
        shell: &mut crate::shell::Shell,
        agent: CellId,
    ) -> Result<crate::surface::SurfaceId, SwarmError> {
        let Some(&idx) = self.index.get(&agent) else {
            return Err(SwarmError::UnknownMember { agent });
        };
        let name = self.members[idx].name.clone();
        let short = self.members[idx].short.clone();
        let cap = shell.open_cell_view(agent, format!("swarm: {name} ({short})"));
        let surface_id = cap.surface();
        self.members[idx].surface = Some(surface_id);
        self.members[idx].surface_cap = Some(cap);
        Ok(surface_id)
    }

    /// The surface capability a member holds over its pane (if bound). This is
    /// the REAL firmament cap — the cockpit presents it to the shell's cap-gated
    /// ops, so the discipline is demonstrated, not bypassed.
    pub fn member_surface_cap(
        &self,
        agent: &CellId,
    ) -> Option<&crate::surface::SurfaceCapability> {
        self.index
            .get(agent)
            .and_then(|&idx| self.members[idx].surface_cap.as_ref())
    }

    /// **RUN A MULTI-EFFECT ATOMIC SWARM TURN** — a coordinator bundles N
    /// member-actions into ONE forest turn the executor commits ALL-OR-NOTHING.
    ///
    /// This is the swarm's *atomic coordination* primitive (distinct from the
    /// async notify edge): where the notify edge is causal-but-independent (A
    /// wakes B; B drains in its own future turn), an atomic swarm turn is a SINGLE
    /// receipted turn carrying several actions across several cells, committed as
    /// a unit — if ANY action is invalid, the WHOLE turn rejects and no partial
    /// effect lands (the `forest_turn` all-or-nothing guarantee). The use: a
    /// coordinator atomically settling a multi-party exchange, or fanning a batch
    /// of in-mandate actions out to several workers in one verified step.
    ///
    /// The coordinator (`agent`) is the turn's signer; each `(target, effects)`
    /// entry is one action in the forest. EVERY effect is cap-gated against the
    /// COORDINATOR's authority (the coordinator must hold a cap reaching each
    /// effect target it does not own) — the atomic turn cannot exceed the
    /// coordinator's mandate. The whole forest then runs through the REAL executor
    /// as one turn; on commit there is ONE receipt for the whole bundle.
    ///
    /// Returns the (single) outcome with the bundle's receipt, or a `SwarmError`
    /// (out-of-mandate / unbacked / executor-rejected — the whole bundle).
    pub fn run_atomic(
        &mut self,
        world: &mut World,
        agent: CellId,
        actions: Vec<(CellId, Vec<dregg_turn::action::Effect>)>,
    ) -> Result<SwarmActionOutcome, SwarmError> {
        // (1) Resolve the coordinator.
        let Some(&idx) = self.index.get(&agent) else {
            return Err(SwarmError::UnknownMember { agent });
        };
        // (2) Confirm the coordinator is backed.
        if world.ledger().get(&agent).is_none() {
            return Err(SwarmError::Unbacked { member: agent });
        }
        // (3) CAP-GATE every effect across every action against the COORDINATOR.
        //     The atomic turn is signed by the coordinator, so its whole reach is
        //     bounded by the coordinator's mandate (a cell reaches itself; any
        //     other target needs a held cap).
        for (_target, effects) in &actions {
            for effect in effects {
                if let Some(t) = effect_target(effect) {
                    if t != agent {
                        let has_cap = world
                            .ledger()
                            .get(&agent)
                            .map(|c| c.capabilities.has_access(&t))
                            .unwrap_or(false);
                        if !has_cap {
                            return Err(SwarmError::OutOfMandate { member: agent, target: t });
                        }
                    }
                }
            }
        }

        // (3b) BUDGET GATE — fail-closed before the bundle runs (same discipline
        //      as `run`): a coordinator at its metered-computron ceiling cannot
        //      dispatch an atomic bundle either. No turn commits, no height advance.
        if self.members[idx].budget.is_exhausted() {
            let b = self.members[idx].budget;
            let ceiling = b.ceiling.unwrap_or(0);
            let ao = SwarmActionOutcome {
                member: agent,
                committed: false,
                receipt_hash: None,
                height: None,
                computrons: 0,
                notify_edges: Vec::new(),
                summary: format!(
                    "ATOMIC bundle REFUSED — budget exhausted (spent {} ≥ ceiling {ceiling})",
                    b.spent
                ),
            };
            self.action_log.push(ao);
            return Err(SwarmError::BudgetExhausted {
                member: agent,
                spent: b.spent,
                ceiling,
                would_be: b.spent,
            });
        }

        // (4) Build + commit ONE atomic forest turn through the REAL executor.
        let dyn_cursor_before = world.dynamics().cursor();
        let turn = world.forest_turn(agent, actions);
        let outcome = world.commit_turn(turn);

        match outcome {
            CommitOutcome::Committed { ref receipt, .. } => {
                let receipt_hash = receipt.receipt_hash();
                let height = world.height();
                let computrons = receipt.computrons_used;

                // (5) Route any inter-member notify edges the bundle produced (a
                //     bundled EmitEvent still wakes a peer — the atomic turn and
                //     the async edge compose).
                let new_events = world.dynamics().since(dyn_cursor_before);
                let mut notify_edges: Vec<(CellId, NotifyEdge)> = Vec::new();
                for ev in new_events {
                    if let WorldEvent::EventEmitted {
                        sender,
                        cell: recipient,
                        topic_hash,
                        data_len,
                    } = ev
                    {
                        if sender == recipient || !self.index.contains_key(recipient) {
                            continue;
                        }
                        notify_edges.push((
                            *recipient,
                            NotifyEdge {
                                from: *sender,
                                turn_height: height,
                                sender_receipt: receipt_hash,
                                topic_hash: *topic_hash,
                                data_len: *data_len,
                                drained: false,
                                drain_receipt: None,
                            },
                        ));
                    }
                }
                for (recipient, edge) in &notify_edges {
                    if let Some(&ridx) = self.index.get(recipient) {
                        self.members[ridx].inbox.insert(0, edge.clone());
                    }
                }

                let summary = format!("ATOMIC bundle · {}", summarize_events(new_events));

                // (6) Refresh the coordinator's counters + grow its budget meter by
                //     the bundle's metered computrons (one receipt, one spend).
                let m = &mut self.members[idx];
                m.action_count += 1;
                m.budget.spent = m.budget.spent.saturating_add(computrons);
                if let Some(c) = world.ledger().get(&agent) {
                    m.balance = c.state.balance();
                }
                m.backed = true;

                let ao = SwarmActionOutcome {
                    member: agent,
                    committed: true,
                    receipt_hash: Some(receipt_hash),
                    height: Some(height),
                    computrons,
                    notify_edges: notify_edges.clone(),
                    summary,
                };
                self.action_log.push(ao.clone());
                Ok(ao)
            }
            CommitOutcome::Rejected { reason, .. } => {
                let ao = SwarmActionOutcome {
                    member: agent,
                    committed: false,
                    receipt_hash: None,
                    height: None,
                    computrons: 0,
                    notify_edges: Vec::new(),
                    summary: format!("ATOMIC bundle REFUSED — {reason}"),
                };
                self.action_log.push(ao.clone());
                Err(SwarmError::ExecutorRejected { member: agent, reason })
            }
        }
    }

    /// **DRAIN A PENDING NOTIFICATION** — the recipient member commits its OWN
    /// separate ack turn (a `SetField` on its own cell), consuming the oldest
    /// pending `NotifyEdge` in its inbox. This is the async drain: the
    /// notification was deposited by the SENDER's committed turn; the drain is
    /// a wholly independent future turn by the RECIPIENT.
    ///
    /// The drain turn IS a real cap-gated turn — the recipient writes a state
    /// field on its own backing cell (always in-mandate, a cell reaches itself)
    /// as the ack. On success, the `NotifyEdge` is marked `drained = true` and
    /// carries the drain receipt.
    ///
    /// Returns the drain turn's receipt hash on success, or a `SwarmError` if
    /// the agent has no pending notifications or the backing cell is gone.
    pub fn drain_notify(
        &mut self,
        world: &mut World,
        agent: CellId,
    ) -> Result<[u8; 32], SwarmError> {
        let Some(&idx) = self.index.get(&agent) else {
            return Err(SwarmError::UnknownMember { agent });
        };
        if world.ledger().get(&agent).is_none() {
            return Err(SwarmError::Unbacked { member: agent });
        }

        // Find the oldest pending notification.
        let pending_pos = self.members[idx].inbox.iter().rposition(|n| n.is_pending());
        let Some(pos) = pending_pos else {
            // Nothing to drain — not an error, just idempotent.
            return Err(SwarmError::ExecutorRejected {
                member: agent,
                reason: "inbox is empty — nothing to drain".to_string(),
            });
        };

        // Run the ack turn: set field[2] on the agent's own cell. This is
        // ALWAYS in-mandate (a cell reaches itself) and always passes the
        // executor (SetField on a live cell with open permissions succeeds).
        // Field index 2 is the "ack slot" (0 = reserved, 1 = buffer digest for
        // BufferCell; 2 = swarm ack counter). The value is the sender receipt
        // hash truncated to 32 bytes — a content-addressed ack.
        let edge = &self.members[idx].inbox[pos];
        let ack_value: [u8; 32] = edge.sender_receipt;
        let ack_effect = world::set_field(agent, 2, ack_value);

        let dyn_cursor = world.dynamics().cursor();
        let turn = world.turn(agent, vec![ack_effect]);
        let drain_outcome = world.commit_turn(turn);

        match drain_outcome {
            CommitOutcome::Committed { ref receipt, .. } => {
                let drain_receipt = receipt.receipt_hash();
                let computrons = receipt.computrons_used;

                // Mark the inbox entry drained.
                self.members[idx].inbox[pos].drained = true;
                self.members[idx].inbox[pos].drain_receipt = Some(drain_receipt);
                self.members[idx].action_count += 1;
                self.members[idx].budget.spent =
                    self.members[idx].budget.spent.saturating_add(computrons);
                if let Some(c) = world.ledger().get(&agent) {
                    self.members[idx].balance = c.state.balance();
                }

                // Log the drain as a swarm action.
                let new_events = world.dynamics().since(dyn_cursor);
                let summary = format!(
                    "DRAIN ack · notify from {} · {}",
                    crate::reflect::short_hex(self.members[idx].inbox[pos].from.as_bytes()),
                    summarize_events(new_events),
                );
                let drain_height = world.height();
                self.action_log.push(SwarmActionOutcome {
                    member: agent,
                    committed: true,
                    receipt_hash: Some(drain_receipt),
                    height: Some(drain_height),
                    computrons,
                    notify_edges: Vec::new(),
                    summary,
                });

                Ok(drain_receipt)
            }
            CommitOutcome::Rejected { reason, .. } => {
                Err(SwarmError::ExecutorRejected { member: agent, reason })
            }
        }
    }

    /// Refresh all member live-state from `world` (balance, backed, action count).
    /// Call after external turns (non-swarm turns that may change cell states).
    pub fn refresh(&mut self, world: &World) {
        for m in &mut self.members {
            m.backed = world.ledger().contains(&m.agent);
            if let Some(c) = world.ledger().get(&m.agent) {
                m.balance = c.state.balance();
            }
            m.action_count = world.receipts().iter().filter(|r| r.agent == m.agent).count();
        }
    }

    /// Snapshot the total pending-notification count across all members.
    pub fn total_pending(&self) -> usize {
        self.members.iter().map(|m| m.pending_notify_count()).sum()
    }

    // ── THE BUDGET METER (N1) ────────────────────────────────────────────────

    /// **Set (or clear) a member's metered-computron ceiling.** `Some(c)` gates
    /// the member: once its `spent` reaches `c`, [`Swarm::run`] /
    /// [`Swarm::run_atomic`] refuse the next dispatch fail-closed
    /// ([`SwarmError::BudgetExhausted`], no turn committed). `None` removes the
    /// gate (unbounded). Returns `false` if the agent is not a member. Setting the
    /// ceiling does NOT reset `spent` — it is the operator declaring the cap on the
    /// already-running conserved spend.
    pub fn set_ceiling(&mut self, agent: &CellId, ceiling: Option<u64>) -> bool {
        match self.index.get(agent) {
            Some(&idx) => {
                self.members[idx].budget.ceiling = ceiling;
                true
            }
            None => false,
        }
    }

    /// A member's live budget meter (its running metered spend + ceiling), or
    /// `None` if the agent is not a member.
    pub fn member_budget(&self, agent: &CellId) -> Option<BudgetMeter> {
        self.index.get(agent).map(|&idx| self.members[idx].budget)
    }

    /// **THE SWARM-AGGREGATE BUDGET** — the conserved spend across all members:
    /// the sum of every member's metered spend, the sum of the SET ceilings, the
    /// headroom over the bounded members, and how many members are bounded. This
    /// is the aggregate meter strip — "could the swarm have cost more than I
    /// allowed?" answered over the bounded subset (a hard conserved bound; the
    /// `dregg_coord::StingrayCounter` single-pool lift is the named N9 weld).
    pub fn swarm_budget(&self) -> SwarmBudget {
        let total_spent: u64 = self
            .members
            .iter()
            .map(|m| m.budget.spent)
            .fold(0u64, |a, s| a.saturating_add(s));
        let total_ceiling: u64 = self
            .members
            .iter()
            .filter_map(|m| m.budget.ceiling)
            .fold(0u64, |a, c| a.saturating_add(c));
        let bounded_members = self
            .members
            .iter()
            .filter(|m| m.budget.ceiling.is_some())
            .count();
        SwarmBudget {
            total_spent,
            total_ceiling,
            headroom: total_ceiling.saturating_sub(total_spent),
            bounded_members,
        }
    }
}

/// THE SWARM VIEW — the gpui-free render model the cockpit maps onto the SWARM
/// tab. Built from the live [`Swarm`] + [`World`]; shows each member's state
/// and the inter-member notify-edge activity feed.
#[derive(Clone, Debug)]
pub struct SwarmView {
    /// The member summaries (boot order — one row per member in the panel).
    pub members: Vec<SwarmMemberView>,
    /// The activity log: recent swarm actions (newest-first, capped at 32).
    pub activity: Vec<SwarmActivityEntry>,
    /// The total pending-notification count across all members.
    pub total_pending: usize,
    /// The swarm's aggregate committed action count.
    pub total_actions: usize,
    /// THE AGGREGATE BUDGET STRIP — total spent / total ceiling / headroom across
    /// the bounded members (`docs/AGENT-SWARM-UX.md` §4.5).
    pub budget: SwarmBudget,
}

/// One member's summary in the SWARM tab panel.
#[derive(Clone, Debug)]
pub struct SwarmMemberView {
    pub agent: CellId,
    pub short: String,
    pub name: String,
    pub backed: bool,
    pub balance: i64,
    pub action_count: usize,
    pub pending_notify: usize,
    /// The inbox (pending-first, then drained) — the most recent 8 entries.
    pub inbox: Vec<NotifyEdge>,
    /// THE BUDGET METER — the member's running metered spend (`budget.spent`)
    /// against its optional `budget.ceiling`. The panel draws this as a bar; it
    /// goes amber as `spent` nears the ceiling and red+REFUSED at exhaustion.
    pub budget: BudgetMeter,
}

/// One entry in the swarm activity feed.
#[derive(Clone, Debug)]
pub struct SwarmActivityEntry {
    /// The member that acted.
    pub member_short: String,
    pub member: CellId,
    /// Whether the action committed.
    pub committed: bool,
    /// The receipt hash (if committed), short-form.
    pub receipt_short: Option<String>,
    /// The height (if committed).
    pub height: Option<u64>,
    /// The action summary (effect labels or refusal reason).
    pub summary: String,
    /// Notify edges produced by this action (inter-member wakes).
    pub notify_edges: Vec<String>,
}

impl SwarmView {
    /// Build the swarm view from the live swarm + world.
    pub fn build(swarm: &Swarm, _world: &World) -> Self {
        let members: Vec<SwarmMemberView> = swarm
            .members()
            .iter()
            .map(|m| {
                let mut inbox: Vec<NotifyEdge> = m.inbox.clone();
                inbox.truncate(8);
                SwarmMemberView {
                    agent: m.agent,
                    short: m.short.clone(),
                    name: m.name.clone(),
                    backed: m.backed,
                    balance: m.balance,
                    action_count: m.action_count,
                    pending_notify: m.pending_notify_count(),
                    inbox,
                    budget: m.budget,
                }
            })
            .collect();

        let total_pending = swarm.total_pending();
        let total_actions: usize = members.iter().map(|m| m.action_count).sum();
        let budget = swarm.swarm_budget();

        let activity: Vec<SwarmActivityEntry> = swarm
            .action_log()
            .iter()
            .rev()
            .take(32)
            .map(|ao| {
                let notify_edges: Vec<String> = ao
                    .notify_edges
                    .iter()
                    .map(|(recipient, edge)| {
                        format!(
                            "→ notify {} topic 0x{}",
                            crate::reflect::short_hex(recipient.as_bytes()),
                            hex::encode(&edge.topic_hash[..4])
                        )
                    })
                    .collect();
                SwarmActivityEntry {
                    member_short: crate::reflect::short_hex(ao.member.as_bytes()),
                    member: ao.member,
                    committed: ao.committed,
                    receipt_short: ao.receipt_hash.map(|h| crate::reflect::short_hex(&h)),
                    height: ao.height,
                    summary: ao.summary.clone(),
                    notify_edges,
                }
            })
            .collect();

        SwarmView {
            members,
            activity,
            total_pending,
            total_actions,
            budget,
        }
    }
}

// ── helpers ──────────────────────────────────────────────────────────────────

/// Extract the primary target cell from an effect (the cell whose authority the
/// cap-gate checks). Returns `None` for effects that are authority-less or have
/// no specific target (e.g. `IncrementNonce`).
fn effect_target(effect: &dregg_turn::action::Effect) -> Option<CellId> {
    use dregg_turn::action::Effect;
    match effect {
        Effect::Transfer { to, .. } => Some(*to),
        Effect::SetField { cell, .. } => Some(*cell),
        // For GrantCapability, the cap-gate checks whether the actor has authority
        // over `from` (the cell whose c-list the grant comes from). When `from ==
        // actor`, this is trivially satisfied; otherwise the actor needs a cap to `from`.
        Effect::GrantCapability { from, .. } => Some(*from),
        Effect::RevokeCapability { cell, .. } => Some(*cell),
        Effect::EmitEvent { cell, .. } => Some(*cell),
        Effect::CellSeal { target, .. } => Some(*target),
        Effect::CellUnseal { target } => Some(*target),
        Effect::CellDestroy { target, .. } => Some(*target),
        Effect::Burn { target, .. } => Some(*target),
        Effect::CreateCell { .. } | Effect::CreateCellFromFactory { .. } => None,
        Effect::MakeSovereign { cell } => Some(*cell),
        _ => None,
    }
}

/// Build a human-meaningful summary of a slice of `WorldEvent`s (the effects
/// of a committed turn — same logic as `describe_committed` in `agent.rs`).
fn summarize_events(events: &[WorldEvent]) -> String {
    let mut parts: Vec<String> = Vec::new();
    for ev in events {
        match ev {
            WorldEvent::BalanceFlowed { before, after, .. } => {
                let d = after - before;
                let sign = if d >= 0 { "+" } else { "" };
                parts.push(format!("flow {sign}{d}"));
            }
            WorldEvent::CapabilityGranted { .. } => parts.push("granted cap".into()),
            WorldEvent::CapabilityRevoked { .. } => parts.push("revoked cap".into()),
            WorldEvent::FieldSet { index, .. } => parts.push(format!("set field[{index}]")),
            WorldEvent::CellBorn { .. } => parts.push("created cell".into()),
            WorldEvent::CellSealed { .. } => parts.push("sealed".into()),
            WorldEvent::CellUnsealed { .. } => parts.push("unsealed".into()),
            WorldEvent::CellDestroyed { .. } => parts.push("destroyed".into()),
            WorldEvent::Burned { amount, .. } => parts.push(format!("burned {amount}")),
            WorldEvent::EventEmitted { cell, .. } => parts.push(format!(
                "emit → {}",
                crate::reflect::short_hex(cell.as_bytes())
            )),
            _ => {}
        }
    }
    if parts.is_empty() {
        "committed".to_string()
    } else {
        parts.join(" · ")
    }
}

// ── tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{emit_event, grant_capability, transfer};

    /// A world with three swarm members: coordinator (holds caps to BOTH peers),
    /// worker-a, worker-b. Seeds a real mandate graph.
    ///
    /// The coordinator is born holding ORIGINAL capabilities to both workers (its
    /// mandate). Both caps are seeded at genesis — a coordinator cannot grant
    /// ITSELF a cap to a worker it does not already hold (that would be an
    /// over-grant the no-amplification rule rejects), so the mandate is installed
    /// at birth, the way a node seeds a genesis cell holding its initial authority.
    fn swarm_world() -> (World, Swarm, CellId, CellId, CellId) {
        let mut world = World::new();
        // worker-a and worker-b exist at genesis (no outbound caps initially).
        let worker_a = world.genesis_cell(0xA0, 5_000);
        let worker_b = world.genesis_cell(0xB0, 5_000);
        // coordinator is born holding ORIGINAL caps to BOTH workers (its mandate),
        // installed at genesis (each `grant` is an original authority, not a
        // re-grant of a held cap — legitimate at the genesis seed).
        let mut coord_cell = crate::world::make_open_cell(0xC0, 10_000);
        coord_cell
            .capabilities
            .grant(worker_a, dregg_cell::AuthRequired::None)
            .expect("free slot for worker_a cap");
        coord_cell
            .capabilities
            .grant(worker_b, dregg_cell::AuthRequired::None)
            .expect("free slot for worker_b cap");
        let coord = world.genesis_install(coord_cell);

        let swarm = Swarm::new(
            &world,
            [
                (coord, "coordinator"),
                (worker_a, "worker-a"),
                (worker_b, "worker-b"),
            ],
        );
        assert_eq!(swarm.len(), 3);
        (world, swarm, coord, worker_a, worker_b)
    }

    // ── THE GROUNDED SEAM: a swarm action runs + receipts ────────────────────

    #[test]
    fn an_in_mandate_swarm_action_commits_and_receipts() {
        let (mut world, mut swarm, coord, worker_a, _) = swarm_world();
        let h0 = world.height();
        let outcome = swarm
            .run(&mut world, coord, vec![transfer(coord, worker_a, 500)])
            .expect("in-mandate transfer must commit");
        assert!(outcome.committed);
        assert!(outcome.receipt_hash.is_some(), "a committed action has a receipt");
        assert_eq!(world.height(), h0 + 1, "a real turn was committed");
        // The value actually moved (not a mock).
        assert_eq!(world.ledger().get(&worker_a).unwrap().state.balance(), 5_500);
        // The action log grows.
        assert_eq!(swarm.action_log().len(), 1);
        assert!(swarm.action_log()[0].committed);
    }

    #[test]
    fn an_out_of_mandate_swarm_action_is_refused() {
        let (mut world, mut swarm, worker_a, _coord, worker_b) = {
            let (w, s, c, wa, wb) = swarm_world();
            (w, s, wa, c, wb)
        };
        // worker_a holds NO cap to worker_b — it is not in worker_a's c-list.
        assert!(!world
            .ledger()
            .get(&worker_a)
            .map(|c| c.capabilities.has_access(&worker_b))
            .unwrap_or(false));
        let r = swarm.run(
            &mut world,
            worker_a,
            vec![transfer(worker_a, worker_b, 100)],
        );
        assert!(
            matches!(r, Err(SwarmError::OutOfMandate { .. })),
            "an out-of-mandate action must be refused, got {r:?}"
        );
        // Fail-closed: no turn committed (the mandate is seeded at genesis, so
        // the world starts at height 0 — a refused action does not advance it).
        assert_eq!(world.height(), 0, "no turn committed — fail-closed");
    }

    // ── THE NOTIFY EDGE: EmitEvent → inbox → async drain ────────────────────

    #[test]
    fn an_emit_event_to_a_member_deposits_a_notify_edge_in_its_inbox() {
        // THE ASYNC NOTIFY EDGE: when coordinator emits an event targeting
        // worker_a, a NotifyEdge lands in worker_a's inbox — NOT a joint turn.
        let (mut world, mut swarm, coord, worker_a, _worker_b) = swarm_world();
        let outcome = swarm
            .run(
                &mut world,
                coord,
                vec![emit_event(worker_a, "task/start", vec![])],
            )
            .expect("emit event to in-mandate target must commit");
        assert!(outcome.committed);
        // worker_a has a pending notification.
        let member_a = swarm.members().iter().find(|m| m.agent == worker_a).unwrap();
        assert_eq!(member_a.pending_notify_count(), 1, "worker_a has one pending wake");
        assert_eq!(outcome.notify_edges.len(), 1, "one notify edge was deposited");
        // The edge carries the sender's receipt hash (the provenance link).
        let (recipient, edge) = &outcome.notify_edges[0];
        assert_eq!(*recipient, worker_a);
        assert_eq!(edge.from, coord);
        assert_eq!(edge.sender_receipt, outcome.receipt_hash.unwrap());
        assert!(!edge.drained, "the edge is pending, not drained");
        assert_eq!(swarm.total_pending(), 1);
    }

    #[test]
    fn the_drain_is_the_recipients_own_separate_turn_not_a_joint_turn() {
        // THE ASYNC MODEL: drain_notify commits worker_a's OWN separate turn
        // (a SetField ack). This is NOT a joint turn with the coordinator's
        // emit — it has its own receipt, its own height, its own provenance.
        let (mut world, mut swarm, coord, worker_a, _) = swarm_world();
        swarm
            .run(&mut world, coord, vec![emit_event(worker_a, "task/start", vec![])])
            .expect("emit must commit");
        let h_before_drain = world.height();
        let drain_receipt = swarm
            .drain_notify(&mut world, worker_a)
            .expect("drain must commit");
        // The drain is a distinct committed turn at a later height.
        assert!(world.height() > h_before_drain, "drain is a separate committed turn");
        // The inbox entry is now drained.
        let member_a = swarm.members().iter().find(|m| m.agent == worker_a).unwrap();
        assert_eq!(member_a.pending_notify_count(), 0, "inbox drained");
        let drained = member_a.inbox.iter().find(|n| n.drained).unwrap();
        assert_eq!(
            drained.drain_receipt,
            Some(drain_receipt),
            "the drain receipt is stored on the edge"
        );
        // The coordinator's send receipt != the drain receipt (independent turns).
        let coordinator_receipt = swarm.action_log()[0].receipt_hash.unwrap();
        assert_ne!(
            drain_receipt, coordinator_receipt,
            "the drain and the sender are INDEPENDENT turns (async, not joint)"
        );
    }

    #[test]
    fn a_self_emit_does_not_deposit_a_notify_edge() {
        // A cell emitting an event on ITSELF (a self-notification) is a valid
        // protocol action (it commits) but does NOT produce an inbox entry —
        // waking yourself is a no-op in the swarm inbox model.
        let (mut world, mut swarm, coord, _, _) = swarm_world();
        let outcome = swarm
            .run(
                &mut world,
                coord,
                vec![emit_event(coord, "self/checkpoint", vec![])],
            )
            .expect("self-emit must commit");
        assert!(outcome.committed);
        assert!(
            outcome.notify_edges.is_empty(),
            "self-emit produces no inbox entry"
        );
        assert_eq!(swarm.total_pending(), 0);
    }

    #[test]
    fn an_emit_to_a_non_member_does_not_deposit_in_the_swarm_inbox() {
        // An emit targeting a cell outside the swarm is a valid protocol action
        // (it commits) but produces no swarm inbox entry — the target is not a
        // swarm member, so there's no inbox to deposit to.
        let mut world = World::new();
        let outsider = world.genesis_cell(0xDD, 0);
        let (coord, _) = world.genesis_cell_with_cap(0xCC, 1_000, outsider);
        let mut swarm = Swarm::new(&world, [(coord, "coordinator")]);
        let outcome = swarm
            .run(
                &mut world,
                coord,
                vec![emit_event(outsider, "ping", vec![])],
            )
            .expect("in-mandate emit to outsider must commit");
        assert!(outcome.committed);
        assert!(
            outcome.notify_edges.is_empty(),
            "emit to a non-member produces no inbox entry"
        );
    }

    #[test]
    fn an_unknown_member_action_returns_unknown_member_error() {
        let (mut world, mut swarm, _, _, _) = swarm_world();
        let stranger = CellId::from_bytes([0x77u8; 32]);
        let r = swarm.run(&mut world, stranger, vec![]);
        assert!(matches!(r, Err(SwarmError::UnknownMember { .. })));
    }

    // ── THE VIEW: the panel model reflects the live swarm ───────────────────

    #[test]
    fn swarm_view_reflects_members_and_activity() {
        let (mut world, mut swarm, coord, worker_a, _worker_b) = swarm_world();
        // Coordinator sends value + emits a wake to worker_a.
        swarm
            .run(&mut world, coord, vec![
                transfer(coord, worker_a, 200),
                emit_event(worker_a, "task/go", vec![]),
            ])
            .expect("combined action must commit");
        // worker_a drains the notification.
        swarm.drain_notify(&mut world, worker_a).expect("drain must commit");

        let view = SwarmView::build(&swarm, &world);
        // Three members in the view.
        assert_eq!(view.members.len(), 3);
        // coordinator took its combined transfer+wake action.
        let coord_view = view.members.iter().find(|m| m.agent == coord).unwrap();
        assert!(coord_view.action_count >= 1, "coordinator took at least one action");
        // worker_a drained the notification.
        let wa_view = view.members.iter().find(|m| m.agent == worker_a).unwrap();
        assert_eq!(wa_view.pending_notify, 0, "worker_a drained its inbox");
        // Activity feed has entries (the combined action + the drain).
        assert!(!view.activity.is_empty(), "the activity feed is non-empty");
        // Total pending is 0 (all drained).
        assert_eq!(view.total_pending, 0);
    }

    // ── ATOMIC SWARM TURNS: a coordinator bundles N actions into ONE turn ────

    #[test]
    fn an_atomic_swarm_turn_commits_several_actions_as_one_receipt() {
        // THE ATOMIC BUNDLE: the coordinator (holds caps to both workers) fans a
        // transfer to worker_a AND a wake to worker_b out in ONE forest turn —
        // committed all-or-nothing, with a SINGLE receipt.
        let (mut world, mut swarm, coord, worker_a, worker_b) = swarm_world();
        let h0 = world.height();
        let outcome = swarm
            .run_atomic(
                &mut world,
                coord,
                vec![
                    (coord, vec![transfer(coord, worker_a, 500)]),
                    (coord, vec![emit_event(worker_b, "batch/go", vec![])]),
                ],
            )
            .expect("the atomic bundle must commit");
        assert!(outcome.committed);
        assert_eq!(world.height(), h0 + 1, "ONE turn committed for the whole bundle");
        // The transfer landed.
        assert_eq!(world.ledger().get(&worker_a).unwrap().state.balance(), 5_500);
        // The bundled wake reached worker_b's inbox.
        let mb = swarm.members().iter().find(|m| m.agent == worker_b).unwrap();
        assert_eq!(mb.pending_notify_count(), 1, "the bundled emit woke worker_b");
        // ONE receipt for the whole bundle.
        assert_eq!(outcome.notify_edges.len(), 1);
        assert!(outcome.summary.contains("ATOMIC"));
    }

    #[test]
    fn an_atomic_swarm_turn_is_all_or_nothing() {
        // ATOMICITY: if ANY action in the bundle is invalid (an overspend), the
        // WHOLE turn rejects and no partial effect lands.
        let (mut world, mut swarm, coord, worker_a, worker_b) = swarm_world();
        let coord_before = world.ledger().get(&coord).unwrap().state.balance();
        let r = swarm.run_atomic(
            &mut world,
            coord,
            vec![
                (coord, vec![transfer(coord, worker_a, 500)]), // fine alone
                (coord, vec![transfer(coord, worker_b, 1_000_000)]), // overspends
            ],
        );
        assert!(matches!(r, Err(SwarmError::ExecutorRejected { .. })), "{r:?}");
        // Atomicity: the first transfer did NOT land.
        assert_eq!(
            world.ledger().get(&coord).unwrap().state.balance(),
            coord_before,
            "no partial effect — the whole atomic bundle rolled back"
        );
        assert_eq!(world.ledger().get(&worker_a).unwrap().state.balance(), 5_000);
    }

    #[test]
    fn an_atomic_swarm_turn_cannot_exceed_the_coordinators_mandate() {
        // The atomic bundle is bounded by the COORDINATOR's mandate: an action
        // targeting a cell the coordinator holds no cap to is refused (the whole
        // bundle), before the executor even runs.
        let (mut world, mut swarm, coord, _wa, _wb) = swarm_world();
        let stranger = world.genesis_cell(0xEE, 0);
        let r = swarm.run_atomic(
            &mut world,
            coord,
            vec![(coord, vec![transfer(coord, stranger, 1)])],
        );
        assert!(
            matches!(r, Err(SwarmError::OutOfMandate { target, .. }) if target == stranger),
            "{r:?}"
        );
        assert_eq!(world.height(), 0, "no turn committed (out-of-mandate, fail-closed)");
    }

    // ── PER-MEMBER SURFACE CAPABILITY: each pane a cap-confined Surface ──────

    #[test]
    fn binding_a_member_to_a_surface_gives_it_a_real_cap_confined_pane() {
        // Each swarm member can be bound to a cap-confined shell surface — the
        // member then holds the REAL firmament SurfaceCapability over its pane,
        // and the shell gates every window op on it.
        let (_world, mut swarm, coord, worker_a, _worker_b) = swarm_world();
        let mut shell = crate::shell::Shell::new();
        // Open a console first (the trusted root the shell needs).
        let _console = shell.open_console(coord, "swarm console");

        // Bind the coordinator + worker_a to panes.
        let coord_surface = swarm.bind_surface(&mut shell, coord).expect("bind coord");
        let wa_surface = swarm.bind_surface(&mut shell, worker_a).expect("bind worker_a");
        assert_ne!(coord_surface, wa_surface, "distinct panes get distinct surfaces");

        // The members now hold their REAL surface caps.
        let coord_cap = swarm.member_surface_cap(&coord).expect("coord holds its cap");
        assert_eq!(coord_cap.surface(), coord_surface);
        // The cap authenticates against the shell (it is the genuine authority).
        assert!(shell.validates(coord_cap), "the member's cap authenticates");

        // The cap-gated discipline fires: a window op with the member's cap is
        // authorized; the focus moves to that pane.
        assert!(shell.focus(coord_cap).is_ok(), "the cap authorizes focus");
        assert_eq!(shell.focused(), Some(coord_surface));

        // worker_a holds its own pane cap (distinct authority).
        let wa_member = swarm.members().iter().find(|m| m.agent == worker_a).unwrap();
        assert!(wa_member.has_surface(), "worker_a is bound to a pane");
    }

    #[test]
    fn multiple_notify_edges_to_same_recipient_all_land_in_inbox() {
        let (mut world, mut swarm, coord, worker_a, _) = swarm_world();
        // Two consecutive emits to worker_a.
        swarm
            .run(&mut world, coord, vec![emit_event(worker_a, "task/1", vec![])])
            .expect("first emit");
        swarm
            .run(&mut world, coord, vec![emit_event(worker_a, "task/2", vec![])])
            .expect("second emit");
        let m = swarm.members().iter().find(|m| m.agent == worker_a).unwrap();
        assert_eq!(m.pending_notify_count(), 2, "both wakes are pending");
        assert_eq!(swarm.total_pending(), 2);
        // Drain them one at a time (oldest first — rposition picks the oldest).
        swarm.drain_notify(&mut world, worker_a).expect("first drain");
        swarm.drain_notify(&mut world, worker_a).expect("second drain");
        let m = swarm.members().iter().find(|m| m.agent == worker_a).unwrap();
        assert_eq!(m.pending_notify_count(), 0, "inbox fully drained");
    }

    // ── N1: THE SWARM BUDGET METER (against the REAL metered executor) ───────
    //
    // The budget meter sums the executor's GENUINE `receipt.computrons_used`. For
    // that to be non-zero (a non-vacuous tooth) the world must meter non-zero
    // costs — so these fixtures use a METERED world (`World::with_costs` +
    // `with_turn_fee`), where committed turns accrue real computrons and the agent
    // pays a real fee. The metering is the production executor's, just non-zero.

    use dregg_turn::ComputronCosts;

    /// A metered swarm: a coordinator holding a big balance + caps to both
    /// workers, over a world that meters `default_costs()` and stamps a fee that
    /// covers a per-turn cost. The coordinator's metered actions grow its `spent`.
    fn metered_swarm_world() -> (World, Swarm, CellId, CellId, CellId) {
        // A real metered world: production cost model, a per-turn fee that covers
        // any single dispatch's cost (the agent pays it from its balance).
        let mut world = World::with_costs(ComputronCosts::default_costs()).with_turn_fee(1_000);
        let worker_a = world.genesis_cell(0xA0, 5_000);
        let worker_b = world.genesis_cell(0xB0, 5_000);
        // The coordinator holds a large balance (it pays the per-turn fee on every
        // dispatch) and original caps to both workers (installed at genesis).
        let mut coord_cell = crate::world::make_open_cell(0xC0, 100_000_000);
        coord_cell
            .capabilities
            .grant(worker_a, dregg_cell::AuthRequired::None)
            .expect("free slot for worker_a cap");
        coord_cell
            .capabilities
            .grant(worker_b, dregg_cell::AuthRequired::None)
            .expect("free slot for worker_b cap");
        let coord = world.genesis_install(coord_cell);
        let swarm = Swarm::new(
            &world,
            [(coord, "coordinator"), (worker_a, "worker-a"), (worker_b, "worker-b")],
        );
        (world, swarm, coord, worker_a, worker_b)
    }

    #[test]
    fn the_metered_world_actually_meters_nonzero_computrons() {
        // PRECONDITION for the budget tests being non-vacuous: a committed action
        // in the metered world has a NON-ZERO metered cost (so `spent` can grow and
        // a ceiling can bite). The exact figure is the executor's real metered cost
        // under `default_costs()` (action_base + effect_base + transfer + the
        // turn's other metered legs) — we assert it is non-zero and STABLE (the
        // same dispatch meters the same cost), not a hard-coded constant (that
        // would couple the test to executor cost internals).
        let (mut world, mut swarm, coord, worker_a, _) = metered_swarm_world();
        let o1 = swarm
            .run(&mut world, coord, vec![transfer(coord, worker_a, 100)])
            .expect("transfer commits in the metered world");
        assert!(o1.committed);
        assert!(o1.computrons > 0, "the metered world meters a non-zero cost");
        // The same dispatch meters the same cost (determinism — the meter is a real
        // accounting of the production cost model, not noise).
        let o2 = swarm
            .run(&mut world, coord, vec![transfer(coord, worker_a, 100)])
            .expect("second transfer commits");
        assert_eq!(o1.computrons, o2.computrons, "metering is deterministic per dispatch");
    }

    #[test]
    fn under_ceiling_an_action_commits_and_spent_grows_by_the_metered_computrons() {
        // POLARITY 1 (under-ceiling COMMITS): a member below its ceiling dispatches
        // a real turn; it commits AND its `spent` grows by EXACTLY the executor's
        // metered computrons (the genuine cost, not a re-derived estimate).
        let (mut world, mut swarm, coord, worker_a, _) = metered_swarm_world();
        // A generous ceiling — the dispatch is well under it.
        assert!(swarm.set_ceiling(&coord, Some(10_000)));
        assert_eq!(swarm.member_budget(&coord).unwrap().spent, 0);
        let h0 = world.height();

        let o1 = swarm
            .run(&mut world, coord, vec![transfer(coord, worker_a, 200)])
            .expect("under-ceiling dispatch must commit");
        assert!(o1.committed);
        assert_eq!(world.height(), h0 + 1, "a real turn committed");
        // `spent` grew by EXACTLY the metered computrons of that turn.
        assert_eq!(
            swarm.member_budget(&coord).unwrap().spent,
            o1.computrons,
            "spent grows by the metered computrons"
        );
        assert!(o1.computrons > 0, "the metered cost is non-zero (non-vacuous)");

        // A second dispatch accumulates: spent == sum of the two metered costs.
        let o2 = swarm
            .run(&mut world, coord, vec![transfer(coord, worker_a, 200)])
            .expect("second under-ceiling dispatch must commit");
        assert_eq!(
            swarm.member_budget(&coord).unwrap().spent,
            o1.computrons + o2.computrons,
            "spent is the running sum of metered computrons"
        );
        // Headroom shrank by the same amount.
        assert_eq!(
            swarm.member_budget(&coord).unwrap().headroom(),
            Some(10_000 - (o1.computrons + o2.computrons)),
        );
    }

    #[test]
    fn a_dispatch_that_would_breach_the_ceiling_is_refused_with_no_height_advance() {
        // POLARITY 2 (breach REFUSED, no commit): once a member has spent up to its
        // ceiling, the NEXT dispatch is refused fail-closed — BudgetExhausted, and
        // the height does NOT advance (no turn committed). This is the runaway
        // refused AT the seam, not reconciled after.
        let (mut world, mut swarm, coord, worker_a, _) = metered_swarm_world();
        // First, run one real action to learn its metered cost, then set the
        // ceiling EXACTLY at that spend so the member is now exhausted.
        let o1 = swarm
            .run(&mut world, coord, vec![transfer(coord, worker_a, 100)])
            .expect("first dispatch commits");
        let spent_after_one = swarm.member_budget(&coord).unwrap().spent;
        assert_eq!(spent_after_one, o1.computrons);
        // Set the ceiling at the current spend: the member is now AT its ceiling.
        assert!(swarm.set_ceiling(&coord, Some(spent_after_one)));
        assert!(swarm.member_budget(&coord).unwrap().is_exhausted());

        let h_before = world.height();
        let log_len_before = swarm.action_log().len();
        let r = swarm.run(&mut world, coord, vec![transfer(coord, worker_a, 100)]);
        // The dispatch is refused with the budget error.
        match r {
            Err(SwarmError::BudgetExhausted { member, spent, ceiling, .. }) => {
                assert_eq!(member, coord);
                assert_eq!(spent, spent_after_one);
                assert_eq!(ceiling, spent_after_one);
            }
            other => panic!("expected BudgetExhausted, got {other:?}"),
        }
        // FAIL-CLOSED: no turn committed — the height did not advance.
        assert_eq!(world.height(), h_before, "no height advance on a budget breach");
        // The spend did NOT change (the refused dispatch metered nothing).
        assert_eq!(swarm.member_budget(&coord).unwrap().spent, spent_after_one);
        // The refusal is RECORDED in the action log (a record, not a silent drop).
        assert_eq!(swarm.action_log().len(), log_len_before + 1);
        let last = swarm.action_log().last().unwrap();
        assert!(!last.committed);
        assert!(last.summary.contains("BUDGET EXHAUSTED"));
    }

    #[test]
    fn an_unbounded_member_is_never_budget_refused() {
        // A member with no ceiling (the default) is never budget-gated — it spends
        // freely (the gate is opt-in per member).
        let (mut world, mut swarm, coord, worker_a, _) = metered_swarm_world();
        assert!(swarm.member_budget(&coord).unwrap().ceiling.is_none());
        // Many dispatches, none refused for budget.
        for _ in 0..5 {
            swarm
                .run(&mut world, coord, vec![transfer(coord, worker_a, 10)])
                .expect("an unbounded member is never budget-refused");
        }
        assert!(swarm.member_budget(&coord).unwrap().spent > 0);
        assert!(!swarm.member_budget(&coord).unwrap().is_exhausted());
    }

    #[test]
    fn the_aggregate_swarm_budget_sums_spends_and_ceilings_correctly() {
        // THE AGGREGATE: total_spent = Σ member spent; total_ceiling = Σ SET
        // ceilings (unbounded members contribute nothing); headroom = ceiling −
        // spent; bounded_members counts the gated subset.
        let (mut world, mut swarm, coord, worker_a, worker_b) = metered_swarm_world();
        // Give worker_a a cap to worker_b so it too can act on a peer (for a
        // second spender). worker_a is born with no outbound cap, so it can only
        // act on ITSELF — a self SetField is metered and in-mandate.
        // Bound the coordinator and worker_a; leave worker_b unbounded.
        assert!(swarm.set_ceiling(&coord, Some(5_000)));
        assert!(swarm.set_ceiling(&worker_a, Some(5_000)));
        let _ = worker_b;

        // Coordinator spends (a transfer to worker_a).
        let oc = swarm
            .run(&mut world, coord, vec![transfer(coord, worker_a, 100)])
            .expect("coord dispatch commits");
        // worker_a spends on ITSELF (a self SetField — always in-mandate, metered).
        let ow = swarm
            .run(&mut world, worker_a, vec![crate::world::set_field(worker_a, 3, [1u8; 32])])
            .expect("worker_a self-action commits");

        let agg = swarm.swarm_budget();
        assert_eq!(agg.bounded_members, 2, "coord + worker_a are bounded");
        assert_eq!(agg.total_ceiling, 10_000, "Σ set ceilings = 5_000 + 5_000");
        assert_eq!(
            agg.total_spent,
            oc.computrons + ow.computrons,
            "total_spent is the sum of every member's metered spend"
        );
        assert_eq!(agg.headroom, 10_000 - (oc.computrons + ow.computrons));

        // The SwarmView surfaces the same aggregate + per-member meter.
        let view = SwarmView::build(&swarm, &world);
        assert_eq!(view.budget, agg, "the view's aggregate matches the swarm's");
        let coord_view = view.members.iter().find(|m| m.agent == coord).unwrap();
        assert_eq!(coord_view.budget.spent, oc.computrons);
        assert_eq!(coord_view.budget.ceiling, Some(5_000));
    }

    #[test]
    fn budget_meter_arithmetic_is_correct_both_polarities() {
        // The pure meter arithmetic (the UI pre-check helpers): an unbounded meter
        // never breaches; a bounded one breaches strictly past the ceiling, admits
        // landing EXACTLY on it, and reports headroom + exhaustion correctly.
        let unbounded = BudgetMeter { spent: 1_000, ceiling: None };
        assert!(!unbounded.would_breach(u64::MAX), "unbounded never breaches");
        assert_eq!(unbounded.headroom(), None);
        assert!(!unbounded.is_exhausted());

        let bounded = BudgetMeter { spent: 80, ceiling: Some(100) };
        assert_eq!(bounded.headroom(), Some(20));
        assert!(!bounded.is_exhausted(), "80 < 100");
        assert!(!bounded.would_breach(20), "lands exactly on the ceiling — admitted");
        assert!(bounded.would_breach(21), "strictly past the ceiling — breaches");

        let at_ceiling = BudgetMeter { spent: 100, ceiling: Some(100) };
        assert!(at_ceiling.is_exhausted(), "spent == ceiling is exhausted");
        assert_eq!(at_ceiling.headroom(), Some(0));
        assert!(at_ceiling.would_breach(1));
    }

    #[test]
    fn the_budget_gate_holds_for_atomic_bundles_too() {
        // The atomic-bundle path (`run_atomic`) honors the SAME budget gate: a
        // coordinator at its ceiling cannot dispatch a bundle either (fail-closed).
        let (mut world, mut swarm, coord, worker_a, worker_b) = metered_swarm_world();
        let o1 = swarm
            .run(&mut world, coord, vec![transfer(coord, worker_a, 100)])
            .expect("first dispatch commits");
        let spent = swarm.member_budget(&coord).unwrap().spent;
        assert_eq!(spent, o1.computrons);
        assert!(swarm.set_ceiling(&coord, Some(spent))); // now exhausted
        let h_before = world.height();
        let r = swarm.run_atomic(
            &mut world,
            coord,
            vec![(coord, vec![transfer(coord, worker_b, 1)])],
        );
        assert!(matches!(r, Err(SwarmError::BudgetExhausted { .. })), "{r:?}");
        assert_eq!(world.height(), h_before, "no atomic turn committed on a breach");
    }
}
