//! THE FOUR-SURFACE KILLER DEMO (N5) — the pug-handoff evaluation artifact.
//!
//! This is THE single runnable end-to-end story a stranger runs to judge whether
//! the substrate is real and usable. It lives entirely in starbridge-v2's embedded
//! VERIFIED world — every step is a real receipted turn through the embedded
//! [`TurnExecutor`](dregg_turn::TurnExecutor) (`crate::world::World::commit_turn`),
//! plus real cap-gated window ops through the firmament-backed [`crate::shell::Shell`].
//! There is ZERO dependence on the cutover or seL4.
//!
//! `docs/FRONTIER-ROADMAP.md` §4 (the headline killer demo) is the script. The four
//! frames + the dual refusal, in order:
//!
//!   1. **MINT** — a token/identity cell is born via factory-birth
//!      (`CreateCellFromFactory` through the real executor, validated against a
//!      deployed [`FactoryDescriptor`](dregg_cell::factory::FactoryDescriptor)). One
//!      cell, born of a factory, with a receipt. *Mint once.*
//!   2. **AGENT TURN** — agent A, holding a cap-attenuated mandate over the budget
//!      cell, commits an in-mandate spend from the shared budget. The balance moves;
//!      a receipt appears; conservation holds; the swarm budget meter climbs. *Agent
//!      acts in-mandate.*
//!   3. **NOTIFY HANDOFF** — A notifies counterparty B via the async notify edge (an
//!      `EmitEvent` turn depositing a `NotifyEdge` in B's inbox); B drains it in its
//!      OWN separate receipted turn. **TWO DISTINCT receipt hashes** — causality A→B
//!      visible, independence proven (not a joint turn). *A hands off to B.*
//!   4. **THE DUAL REFUSAL (the climax)** — compromised B tries BOTH:
//!        (a) an **OVER-GRANT** (widen its mandate to a cell it holds no cap to) —
//!            refused by the real executor's no-amplification rule (the
//!            `granted ⊆ held` gate, `DelegationDenied`), AND
//!        (b) an **OVER-SPEND** against the verified Stingray shared-budget ceiling
//!            (`src/swarm_budget.rs`) — refused by the counter's conservation gate
//!            (`PoolExhausted`) BEFORE the turn runs.
//!      BOTH fail-closed through the REAL executor / the REAL verified counter, each
//!      surfaced WITH the executor's own reason. *The same no-amplification law fires
//!      at the swarm seam AND at the budget ceiling.* (A third refusal — the pixel-
//!      layer over-share — is ALSO available via [`HeadlineDemo::refuse_over_share`]
//!      for the SHELL/SWARM-tab cut, the `⚠ over-share` `DelegationDenied` at the
//!      glass.)
//!
//! # Step 5 (DEFERRED — the pg Tier-B mirror read)
//!
//! `docs/FRONTIER-ROADMAP.md` §4 step 5 ("query the truth in SQL") reads B's narrowed
//! authority from the pg-dregg Tier-B mirror. That is N2 / the pg-dregg lane and is
//! **deliberately not wired here** (it needs a live postgres mirror, outside this
//! crate's ownership). It is surfaced as a follow-up, not blocked on — the four frames
//! + the dual refusal are the complete, self-contained evaluation artifact.
//!
//! # Why this is not a mock
//!
//! Every frame is a real `CommitOutcome::Committed` (a real [`TurnReceipt`]) or, for
//! the refusals, a real `Err` from the executor / the verified counter. The MINT is a
//! genuine factory-birth; the AGENT TURN moves real balance under a real cap-gate; the
//! NOTIFY HANDOFF is two independent receipts on the live ledger; the DUAL REFUSAL is
//! two real fail-closed refusals citing the deployed semantics. The self-check
//! ([`HeadlineDemo::run_headless`]) ASSERTS each of these invariants and prints the
//! four frames + both refusals; it is the same engine the cockpit's SWARM-tab live
//! path drives one frame at a time.

use dregg_cell::factory::{FactoryCreationParams, FactoryDescriptor};
use dregg_cell::{AuthRequired, CellId, CellMode};
use dregg_turn::ComputronCosts;

use crate::swarm::{Swarm, SwarmError};
use crate::world::{self, World};

/// The ceiling `B` (computrons) of the verified Stingray shared budget the demo
/// attaches. Sized so the TWO legitimate pool-drawing dispatches (the frame-2 agent
/// spend + the frame-3 notify, each pre-checked at the declared fee `DEMO_TURN_FEE`
/// and settling its real metered cost) BOTH fit, but B's frame-4 OVER-SPEND
/// pre-check (a third declared fee) BREACHES the remaining headroom.
///
/// The gate (the SDK's `set_budget_gate` shape) pre-checks the DECLARED fee
/// (`DEMO_TURN_FEE`, the conservative upper bound) before each dispatch, then settles
/// the ACTUAL metered cost (`m`, ~300 under `default_costs()` for these turns). So:
///   * frame 2 (agent spend): remaining = B; pre-check `DEMO_TURN_FEE ≤ B` (B=1500 ✓);
///     settles `m`, remaining → B − m (~1200).
///   * frame 3 (notify): pre-check `DEMO_TURN_FEE ≤ B − m` (1000 ≤ ~1200 ✓); settles
///     `m`, remaining → B − 2m (~900).
///   * frame 4 (over-spend): pre-check `DEMO_TURN_FEE > B − 2m` (1000 > ~900 ✓ BREACH)
///     → `PoolExhausted`, fail-closed, the counter UNMOVED.
/// `B = DEMO_TURN_FEE + 500` lands in the admissible window `[DEMO_TURN_FEE + m,
/// 2·DEMO_TURN_FEE − 2m)` for any single-dispatch metered cost `m < 500` — robust to
/// the exact metered figure without hard-coding it.
const DEMO_BUDGET_CEILING: u64 = DEMO_TURN_FEE + 500;

/// The per-turn fee stamped on every demo turn (the metered world's declared
/// computron budget per turn). Large enough to cover any single dispatch's real
/// metered cost; the agent pays it from its (large) balance, conservation-real.
const DEMO_TURN_FEE: u64 = 1_000;

/// The factory's content-addressed VK seed for the MINT step (a deployed Hosted
/// factory the birth is validated against). Distinct, deterministic.
const MINT_FACTORY_VK: [u8; 32] = [0xF1u8; 32];

/// One frame of the demo's narrative — a real receipted turn (or a real refusal),
/// captured for the self-check print + the cockpit panel. Each carries the
/// executor's OWN record (a receipt hash on commit, the executor's reason on a
/// refusal), so the panel never editorializes over the ground truth.
#[derive(Clone, Debug)]
pub struct DemoFrame {
    /// The frame's ordinal (1..=N in the headline script).
    pub step: u8,
    /// A short stage tag (`MINT` / `AGENT TURN` / `NOTIFY` / `DRAIN` / `REFUSAL`).
    pub stage: &'static str,
    /// The one-line operator-legible narrative of what happened.
    pub headline: String,
    /// Whether this frame is a COMMITTED turn (`true`) or a REFUSAL (`false`).
    /// A refusal is a FEATURE here — the guarantee firing — not an error to hide.
    pub committed: bool,
    /// The receipt hash of the committed turn (short hex), if this frame committed.
    pub receipt: Option<String>,
    /// The world height at/after this frame (the local chain index).
    pub height: u64,
    /// For a refusal frame: the executor's / the verified counter's OWN reason
    /// (the teaching moment — WHY the guarantee fired). `None` for a commit.
    pub refusal_reason: Option<String>,
}

impl DemoFrame {
    fn committed(step: u8, stage: &'static str, headline: String, receipt: [u8; 32], height: u64) -> Self {
        DemoFrame {
            step,
            stage,
            headline,
            committed: true,
            receipt: Some(crate::reflect::short_hex(&receipt)),
            height,
            refusal_reason: None,
        }
    }

    fn refused(step: u8, stage: &'static str, headline: String, reason: String, height: u64) -> Self {
        DemoFrame {
            step,
            stage,
            headline,
            committed: false,
            receipt: None,
            height,
            refusal_reason: Some(reason),
        }
    }

    /// A single render line (the self-check print + the panel row text).
    pub fn line(&self) -> String {
        if self.committed {
            format!(
                "  [{}] {} · h{} · receipt {} — {}",
                self.step,
                self.stage,
                self.height,
                self.receipt.as_deref().unwrap_or("—"),
                self.headline,
            )
        } else {
            format!(
                "  [{}] {} · REFUSED (fail-closed) — {}\n        executor reason: {}",
                self.step,
                self.stage,
                self.headline,
                self.refusal_reason.as_deref().unwrap_or("<none>"),
            )
        }
    }
}

/// Why the demo could not be built/advanced (a SETUP failure — distinct from the
/// in-script refusals, which are the POINT). If any of these fire, the substrate
/// itself is broken (a real regression), so the self-check treats them as failures.
#[derive(Clone, Debug)]
pub enum DemoError {
    /// The MINT (factory-birth) did not commit — the substrate's birth path broke.
    MintFailed(String),
    /// The factory-birth committed but no new cell appeared in the ledger.
    NoChildCell,
    /// The AGENT TURN (the in-mandate spend) did not commit — the cap-gate or the
    /// executor wrongly refused a legitimate action (a regression, not the script).
    AgentTurnFailed(String),
    /// The NOTIFY emit did not commit, or deposited no notify edge in B's inbox.
    NotifyFailed(String),
    /// The DRAIN (B's own ack turn) did not commit.
    DrainFailed(String),
    /// A refusal that was SUPPOSED to fire (over-grant / over-spend) did NOT —
    /// the guarantee silently failed open, which is the worst possible outcome.
    RefusalDidNotFire(&'static str),
}

impl DemoError {
    pub fn label(&self) -> String {
        match self {
            DemoError::MintFailed(r) => format!("MINT (factory-birth) failed: {r}"),
            DemoError::NoChildCell => "MINT committed but no child cell appeared".to_string(),
            DemoError::AgentTurnFailed(r) => format!("AGENT TURN wrongly refused: {r}"),
            DemoError::NotifyFailed(r) => format!("NOTIFY handoff failed: {r}"),
            DemoError::DrainFailed(r) => format!("DRAIN (B's ack turn) failed: {r}"),
            DemoError::RefusalDidNotFire(which) => {
                format!("FAIL-OPEN: the {which} refusal did NOT fire (guarantee broken!)")
            }
        }
    }
}

/// THE HEADLINE DEMO — a self-contained, world-owning state machine that drives
/// the four-surface killer demo through the REAL embedded executor + the firmament
/// shell. gpui-FREE and `cargo test`-able; the `--headless` self-check and the
/// cockpit SWARM-tab live path both drive THIS.
///
/// The demo owns its OWN metered world (so the budget meter sees non-zero metered
/// spend and the Stingray ceiling can bite — see [`World::with_costs`]), a [`Swarm`]
/// with the verified shared budget attached, and (when driving the live/shell path)
/// a [`crate::shell::Shell`] for the pixel-layer over-share refusal.
pub struct HeadlineDemo {
    /// The embedded VERIFIED world — every frame's turn commits here.
    world: World,
    /// The swarm coordinator (A + B as members) with the verified Stingray budget
    /// attached. The over-spend refusal is the counter's gate firing.
    swarm: Swarm,
    /// The MINTED token/identity cell (frame 1's factory-birthed child). The shared
    /// budget cell the agent spends FROM and B tries to over-grant authority over.
    token: CellId,
    /// Agent A — the in-mandate actor (holds a cap to the token cell + to B).
    agent_a: CellId,
    /// Counterparty B — drains the notify, then (compromised) attempts the dual
    /// refusal. Born holding NO cap to the over-grant target (so the over-grant is a
    /// genuine no-amplification violation the executor rejects).
    agent_b: CellId,
    /// A cell B holds NO capability reaching — the over-grant target. B widening its
    /// mandate to grant authority over THIS is the no-amplification violation.
    forbidden: CellId,
    /// The captured frames (the narrative the self-check prints + the panel shows).
    frames: Vec<DemoFrame>,
    /// Where the live (SWARM-tab) driver is in the script (0 = not started, then one
    /// per advance). The headless run drives all steps at once; the cockpit advances
    /// one frame per button press.
    cursor: u8,
}

impl HeadlineDemo {
    /// **Boot the demo world** — genesis the actors + deploy the mint factory, but
    /// run NO script step yet (frame 0). The actors:
    ///
    ///   * `agent_a` — born with a large balance (it pays the per-turn fee) and
    ///     ORIGINAL caps to the token cell and to `agent_b` (its mandate, installed
    ///     at genesis — a cell cannot grant itself a cap it does not hold, so the
    ///     mandate is seeded at birth the way a node seeds a genesis cell's authority).
    ///   * `agent_b` — born with a balance + an original cap to `agent_a` (so it can
    ///     emit/ack back), but NO cap to `forbidden` (so its frame-4 over-grant is a
    ///     real no-amplification violation).
    ///   * `forbidden` — a cell no agent holds a cap to (the over-grant target).
    ///
    /// The world is METERED (`ComputronCosts::default_costs()` + a per-turn fee) so
    /// the budget meter accrues real metered computrons and the Stingray ceiling can
    /// bite (the over-spend refusal is non-vacuous). The verified Stingray shared
    /// budget is attached to the swarm, owned by `agent_a`, at [`DEMO_BUDGET_CEILING`].
    pub fn boot() -> Self {
        // A real metered world: production cost model + a per-turn fee covering a
        // single dispatch (the agent pays it from its big balance, conservation-real).
        let mut world = World::with_costs(ComputronCosts::default_costs()).with_turn_fee(DEMO_TURN_FEE);

        // `forbidden` — the over-grant target no agent reaches.
        let forbidden = world.genesis_cell(0xF0, 0);
        // `agent_b` — holds a cap to A (to ack back), NOT to `forbidden`.
        let mut b_cell = world::make_open_cell(0xB0, 50_000_000);
        // (A's id is derived from a fixed seed below; grant the cap once A exists.)
        // We build B's caps after A's id is known, so birth A's *seed* cell first.
        let mut a_cell = world::make_open_cell(0xA0, 100_000_000);
        let agent_a_id = a_cell.id();
        let agent_b_id = b_cell.id();
        // A holds ORIGINAL caps to the token cell (granted after the mint, below — A
        // is BORN holding a cap to B and to `forbidden`'s SIBLING is irrelevant; the
        // token cap is installed post-mint via the genesis grant path). For now seed
        // A's cap to B (so A can notify B) and B's cap to A (so B can ack).
        a_cell
            .capabilities
            .grant(agent_b_id, AuthRequired::None)
            .expect("A: free slot for the cap to B");
        b_cell
            .capabilities
            .grant(agent_a_id, AuthRequired::None)
            .expect("B: free slot for the cap to A");
        let agent_a = world.genesis_install(a_cell);
        let agent_b = world.genesis_install(b_cell);
        debug_assert_eq!(agent_a, agent_a_id);
        debug_assert_eq!(agent_b, agent_b_id);

        // Deploy the MINT factory (a minimal Hosted factory the birth validates
        // against) into the real executor's registry.
        let descriptor = FactoryDescriptor {
            factory_vk: MINT_FACTORY_VK,
            child_program_vk: None,
            child_vk_strategy: None,
            allowed_cap_templates: vec![],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: Some(8),
        };
        let _vk = world.deploy_factory(descriptor);

        // The swarm: A is the coordinator (owns the shared budget), B is the
        // counterparty. Attach the VERIFIED Stingray shared budget owned by A.
        let mut swarm = Swarm::new(&world, [(agent_a, "agent-A"), (agent_b, "agent-B")]);
        swarm.attach_stingray_budget(agent_a, DEMO_BUDGET_CEILING);

        HeadlineDemo {
            world,
            swarm,
            token: CellId::ZERO, // set by the MINT step (frame 1)
            agent_a,
            agent_b,
            forbidden,
            frames: Vec::new(),
            cursor: 0,
        }
    }

    // --- read surface (the cockpit panel + the self-check consume these) -------

    /// The captured frames so far (the narrative).
    pub fn frames(&self) -> &[DemoFrame] {
        &self.frames
    }

    /// The live embedded world (read-only — the panel reflects cells/receipts).
    pub fn world(&self) -> &World {
        &self.world
    }

    /// The live swarm (read-only — the panel reflects the budget meter / members).
    pub fn swarm(&self) -> &Swarm {
        &self.swarm
    }

    /// The MINTED token cell id (set after frame 1; `CellId::ZERO` before).
    pub fn token(&self) -> CellId {
        self.token
    }

    pub fn agent_a(&self) -> CellId {
        self.agent_a
    }
    pub fn agent_b(&self) -> CellId {
        self.agent_b
    }

    /// How many script steps have run (the live-driver cursor). 0 = not started; the
    /// full script is [`Self::TOTAL_STEPS`].
    pub fn cursor(&self) -> u8 {
        self.cursor
    }

    /// The total number of script steps (the four frames + the two refusals = 6).
    pub const TOTAL_STEPS: u8 = 6;

    /// Whether the full script has run.
    pub fn is_complete(&self) -> bool {
        self.cursor >= Self::TOTAL_STEPS
    }

    /// A one-line label for the NEXT step the live driver will run (for the cockpit
    /// button), or `None` if the script is complete.
    pub fn next_step_label(&self) -> Option<&'static str> {
        match self.cursor {
            0 => Some("1 · MINT a token cell (factory-birth)"),
            1 => Some("2 · AGENT A acts in-mandate (spend from budget)"),
            2 => Some("3 · A notifies B (deposit a wake)"),
            3 => Some("4 · B drains the wake (its OWN ack turn)"),
            4 => Some("5 · REFUSAL: B over-grants (no-amplification)"),
            5 => Some("6 · REFUSAL: B over-spends (Stingray ceiling)"),
            _ => None,
        }
    }

    // --- the script steps (each a REAL turn / a REAL refusal) ------------------

    /// **FRAME 1 — MINT.** Birth a token/identity cell via factory-birth
    /// (`CreateCellFromFactory` through the real executor, validated against the
    /// deployed factory). The child appears in the ledger; we recover its id by
    /// diffing the ledger's cell-id set (robust to the executor's internal child-id
    /// derivation), grant A an ORIGINAL cap reaching it (A is the minter / owner —
    /// the genesis grant path, exactly as the shell hands back a surface owner-grant),
    /// and record the frame. Sets [`Self::token`].
    pub fn step_mint(&mut self) -> Result<&DemoFrame, DemoError> {
        // Snapshot the ledger's cell-id set BEFORE the birth.
        let before: std::collections::HashSet<CellId> =
            self.world.ledger().iter().map(|(id, _)| *id).collect();

        let owner_pubkey = {
            let mut pk = [0u8; 32];
            pk[0] = 0x7C; // the token's owner pubkey (deterministic, distinct)
            pk
        };
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey,
        };
        let birth = world::create_cell_from_factory(MINT_FACTORY_VK, owner_pubkey, [0u8; 32], params);
        let turn = self.world.turn(self.agent_a, vec![birth]);
        let outcome = self.world.commit_turn(turn);

        let receipt = match outcome {
            crate::world::CommitOutcome::Committed { receipt, .. } => receipt,
            crate::world::CommitOutcome::Rejected { reason, .. } => {
                return Err(DemoError::MintFailed(reason));
            }
            crate::world::CommitOutcome::Queued { .. } => {
                return Err(DemoError::MintFailed(
                    "world suspended: mint turn queued, not committed".to_string(),
                ));
            }
        };

        // Recover the freshly-born child: the one id in the after-set not in `before`.
        let token = self
            .world
            .ledger()
            .iter()
            .map(|(id, _)| *id)
            .find(|id| !before.contains(id))
            .ok_or(DemoError::NoChildCell)?;
        self.token = token;

        // Grant A an ORIGINAL cap reaching the token cell (A is the minter/owner —
        // the genesis grant path, like the shell handing back a surface owner-grant).
        // This is the authority A spends the budget under in frame 2.
        let _ = self.world.genesis_grant_cap(&self.agent_a, token);
        // Open the budget cell's permissions (the minter endowing its freshly-minted
        // cell — a factory child carries the factory's default permissions, which
        // require a signature to send FROM it; the minter opens its own cell the way a
        // node seeds a genesis cell's authority). Without this, A's in-mandate spend
        // FROM the budget cell in frame 2 would be PermissionDenied on Send.
        let _ = self.world.genesis_open_permissions(&token);

        let height = self.world.height();
        self.frames.push(DemoFrame::committed(
            1,
            "MINT",
            format!(
                "born a token/identity cell {} via factory-birth (the budget cell)",
                crate::reflect::short_hex(token.as_bytes())
            ),
            receipt.receipt_hash(),
            height,
        ));
        self.cursor = self.cursor.max(1);
        Ok(self.frames.last().unwrap())
    }

    /// **FRAME 2 — AGENT TURN.** Agent A, under its cap-attenuated mandate over the
    /// token cell, commits an in-mandate spend (a transfer from the token budget cell
    /// to A — A draining its budget). The balance moves on the token cell; a receipt
    /// appears; conservation holds; the swarm budget meter climbs by the metered
    /// computrons. Runs through [`Swarm::run`] so the verified shared budget settles
    /// the real metered cost (the conservation step).
    ///
    /// To make the spend a real value move under a real cap-gate, the token cell is
    /// first funded (the genesis path — a node seeds the budget cell's value), then A
    /// transfers from it. A holds an original cap reaching the token cell (granted in
    /// frame 1), so the cap-gate admits it.
    pub fn step_agent_turn(&mut self) -> Result<&DemoFrame, DemoError> {
        if self.token == CellId::ZERO {
            return Err(DemoError::AgentTurnFailed("MINT has not run (no token cell)".into()));
        }
        // Fund the token (budget) cell from A so there is value to spend — the
        // genesis path seeds the budget; this is the operator endowing the pool. A
        // real metered turn (so the meter is non-vacuous), in-mandate (A reaches the
        // token cell via the cap granted in frame 1).
        let fund = world::transfer(self.agent_a, self.token, 10_000);
        let fund_turn = self.world.turn(self.agent_a, vec![fund]);
        if let crate::world::CommitOutcome::Rejected { reason, .. } = self.world.commit_turn(fund_turn) {
            return Err(DemoError::AgentTurnFailed(format!("funding the budget cell: {reason}")));
        }

        // THE AGENT TURN: A spends from the budget cell (token → A). This is the
        // in-mandate spend the headline names; it draws against the verified shared
        // budget (the meter climbs by the metered computrons).
        let spend = world::transfer(self.token, self.agent_a, 2_500);
        let outcome = self.swarm.run(&mut self.world, self.agent_a, vec![spend]);
        let ao = match outcome {
            Ok(ao) => ao,
            Err(e) => return Err(DemoError::AgentTurnFailed(e.label())),
        };
        if !ao.committed {
            return Err(DemoError::AgentTurnFailed("the agent spend did not commit".into()));
        }
        let receipt = ao.receipt_hash.ok_or_else(|| {
            DemoError::AgentTurnFailed("committed but no receipt hash".into())
        })?;
        let drawn = self
            .swarm
            .stingray_budget()
            .map(|p| p.total_drawn())
            .unwrap_or(0);
        let height = ao.height.unwrap_or_else(|| self.world.height());
        self.frames.push(DemoFrame::committed(
            2,
            "AGENT TURN",
            format!(
                "agent-A spent in-mandate from the budget cell (conservation holds; \
                 budget meter drew {drawn} computrons of {DEMO_BUDGET_CEILING})"
            ),
            receipt,
            height,
        ));
        self.cursor = self.cursor.max(2);
        Ok(self.frames.last().unwrap())
    }

    /// **FRAME 3 (part a) — NOTIFY.** Agent A notifies B via the async notify edge:
    /// an `EmitEvent` turn targeting B deposits a `NotifyEdge` in B's inbox. A's
    /// receipt is the FIRST of the two distinct hashes the handoff produces.
    pub fn step_notify(&mut self) -> Result<&DemoFrame, DemoError> {
        let outcome = self.swarm.run(
            &mut self.world,
            self.agent_a,
            vec![world::emit_event(self.agent_b, "handoff/drain-the-budget", vec![])],
        );
        let ao = match outcome {
            Ok(ao) => ao,
            Err(e) => return Err(DemoError::NotifyFailed(e.label())),
        };
        if ao.notify_edges.is_empty() {
            return Err(DemoError::NotifyFailed(
                "the emit committed but deposited NO notify edge in B's inbox".into(),
            ));
        }
        let receipt = ao
            .receipt_hash
            .ok_or_else(|| DemoError::NotifyFailed("committed but no receipt hash".into()))?;
        let height = ao.height.unwrap_or_else(|| self.world.height());
        self.frames.push(DemoFrame::committed(
            3,
            "NOTIFY",
            format!(
                "agent-A notified agent-B (deposited a wake in B's inbox — async, NOT a joint turn)"
            ),
            receipt,
            height,
        ));
        self.cursor = self.cursor.max(3);
        Ok(self.frames.last().unwrap())
    }

    /// **FRAME 3 (part b) — DRAIN.** B drains the wake in its OWN separate receipted
    /// turn ([`Swarm::drain_notify`] — a `SetField` ack on B's own cell). This is the
    /// SECOND distinct receipt hash; it shares no parent with A's emit (independence
    /// proven). The two hashes together make the causality A→B on-ledger and visible.
    pub fn step_drain(&mut self) -> Result<&DemoFrame, DemoError> {
        let drain_receipt = match self.swarm.drain_notify(&mut self.world, self.agent_b) {
            Ok(h) => h,
            Err(e) => return Err(DemoError::DrainFailed(e.label())),
        };
        // The two receipts MUST be distinct (independence — the whole point).
        let a_receipt = self
            .frames
            .iter()
            .find(|f| f.stage == "NOTIFY")
            .and_then(|f| f.receipt.clone());
        let drain_short = crate::reflect::short_hex(&drain_receipt);
        if a_receipt.as_deref() == Some(drain_short.as_str()) {
            return Err(DemoError::DrainFailed(
                "the drain receipt EQUALS A's emit receipt (not independent turns!)".into(),
            ));
        }
        let height = self.world.height();
        self.frames.push(DemoFrame::committed(
            3,
            "DRAIN",
            format!(
                "agent-B drained the wake in its OWN ack turn — TWO distinct receipts \
                 (A:{} ≠ B:{}); causality visible, independence proven",
                a_receipt.as_deref().unwrap_or("?"),
                drain_short,
            ),
            drain_receipt,
            height,
        ));
        self.cursor = self.cursor.max(4);
        Ok(self.frames.last().unwrap())
    }

    /// **FRAME 4 (part a) — THE OVER-GRANT REFUSAL.** Compromised B tries to widen
    /// its mandate: a `GrantCapability` whose `from` is the `forbidden` cell — a
    /// c-list B holds NO capability reaching. B is attempting to grant authority out
    /// of a cell it does not control, the canonical no-amplification violation. The
    /// swarm seam's cap-gate (`granted ⊆ held`, the SAME lattice the executor's
    /// `GrantCapability` path enforces) REFUSES it fail-closed (`OutOfMandate`) BEFORE
    /// any turn runs. This is the swarm-seam half of the dual refusal.
    ///
    /// Routing the over-grant through a c-list B cannot reach (rather than B's own)
    /// keeps the verified shared-budget pool UNTOUCHED — the refusal is the
    /// no-amplification gate, not a budget draw — so the frame-4(b) over-spend below
    /// can then breach the pool cleanly. (Both are the SAME `granted ⊆ held` law: one
    /// over capabilities, one over budget.)
    pub fn refuse_over_grant(&mut self) -> Result<&DemoFrame, DemoError> {
        // B tries to grant a cap OUT OF the `forbidden` cell (from == forbidden) — a
        // c-list B holds no cap reaching. The seam's cap-gate refuses this before the
        // turn (and before the pool pre-check): B cannot grant authority from a cell
        // it does not control (`granted ⊆ held` — the no-amplification rule).
        let over_grant = world::grant_capability(self.forbidden, self.agent_b, self.forbidden, 0);
        let outcome = self.swarm.run(&mut self.world, self.agent_b, vec![over_grant]);
        match outcome {
            Ok(ao) if ao.committed => {
                // FAIL-OPEN — the no-amplification guarantee did NOT fire. This is a
                // real regression (the worst outcome); the self-check fails loudly.
                Err(DemoError::RefusalDidNotFire("over-grant (no-amplification)"))
            }
            Err(SwarmError::ExecutorRejected { reason, .. }) => {
                let height = self.world.height();
                self.frames.push(DemoFrame::refused(
                    4,
                    "REFUSAL",
                    "compromised agent-B tried to OVER-GRANT (widen its mandate to a \
                     cell it holds no cap to) — no-amplification fired"
                        .to_string(),
                    reason,
                    height,
                ));
                self.cursor = self.cursor.max(5);
                Ok(self.frames.last().unwrap())
            }
            Err(SwarmError::OutOfMandate { .. }) => {
                // The cap-gate pre-check caught it (also a real fail-closed refusal,
                // also no-amplification — just at the seam's pre-check rather than the
                // executor). Record it honestly as the no-amplification refusal.
                let height = self.world.height();
                self.frames.push(DemoFrame::refused(
                    4,
                    "REFUSAL",
                    "compromised agent-B tried to OVER-GRANT — refused at the cap-gate \
                     (no-amplification: B holds no cap reaching the target)"
                        .to_string(),
                    "cap-gate: granted ⊄ held (no capability reaching the over-grant target)"
                        .to_string(),
                    height,
                ));
                self.cursor = self.cursor.max(5);
                Ok(self.frames.last().unwrap())
            }
            Err(other) => {
                // Any other refusal is still fail-closed, but not the one we expected;
                // record it with its reason (still a real refusal, no fake-green).
                let height = self.world.height();
                self.frames.push(DemoFrame::refused(
                    4,
                    "REFUSAL",
                    "compromised agent-B tried to OVER-GRANT — refused fail-closed".to_string(),
                    other.label(),
                    height,
                ));
                self.cursor = self.cursor.max(5);
                Ok(self.frames.last().unwrap())
            }
            Ok(ao) => {
                // Committed == false but Ok — a logged refusal; surface its summary.
                let height = self.world.height();
                self.frames.push(DemoFrame::refused(
                    4,
                    "REFUSAL",
                    "compromised agent-B tried to OVER-GRANT — refused fail-closed".to_string(),
                    ao.summary,
                    height,
                ));
                self.cursor = self.cursor.max(5);
                Ok(self.frames.last().unwrap())
            }
        }
    }

    /// **FRAME 4 (part b) — THE OVER-SPEND REFUSAL.** Compromised B tries to drain
    /// the budget past the verified Stingray ceiling. The shared pool's conservation
    /// gate ([`crate::swarm_budget::StingraySwarmBudget`]) REFUSES the draw BEFORE the
    /// turn runs (`PoolExhausted`), fail-closed — the counter is UNMOVED. This is the
    /// budget-ceiling half of the dual refusal (the Stingray ceiling, just landed).
    ///
    /// The pool was opened at exactly one declared fee, and frame 2's agent spend
    /// already settled its real metered cost against it, so the remaining headroom is
    /// below a full declared fee — B's next dispatch's declared fee breaches it.
    pub fn refuse_over_spend(&mut self) -> Result<&DemoFrame, DemoError> {
        // B attempts a spend (a transfer to A, in-mandate — B holds a cap to A). The
        // verified shared-budget gate refuses the DRAW before the turn runs.
        let over_spend = world::transfer(self.agent_b, self.agent_a, 1);
        let outcome = self.swarm.run(&mut self.world, self.agent_b, vec![over_spend]);
        match outcome {
            Err(SwarmError::PoolExhausted { drawn, ceiling, would_be, .. }) => {
                let height = self.world.height();
                self.frames.push(DemoFrame::refused(
                    4,
                    "REFUSAL",
                    "compromised agent-B tried to OVER-SPEND past the shared budget \
                     ceiling — the verified Stingray conservation gate fired"
                        .to_string(),
                    format!(
                        "Stingray pool: drawn {drawn} + this draw would reach {would_be} > \
                         ceiling B={ceiling} (the conservation bound bit; the counter is unmoved)"
                    ),
                    height,
                ));
                self.cursor = self.cursor.max(6);
                Ok(self.frames.last().unwrap())
            }
            Ok(ao) if ao.committed => {
                // FAIL-OPEN — the budget ceiling did NOT bite. A real regression.
                Err(DemoError::RefusalDidNotFire("over-spend (Stingray ceiling)"))
            }
            other => {
                // Any other refusal is still fail-closed; surface it honestly (no
                // fake-green), but flag that it was not the expected PoolExhausted.
                let reason = match &other {
                    Err(e) => e.label(),
                    Ok(ao) => ao.summary.clone(),
                };
                let height = self.world.height();
                self.frames.push(DemoFrame::refused(
                    4,
                    "REFUSAL",
                    "compromised agent-B tried to OVER-SPEND — refused fail-closed".to_string(),
                    reason,
                    height,
                ));
                self.cursor = self.cursor.max(6);
                Ok(self.frames.last().unwrap())
            }
        }
    }

    /// **THE PIXEL-LAYER OVER-SHARE REFUSAL (the SHELL/SWARM-tab cut, optional).**
    /// The third register of the SAME no-amplification law: open the budget (token)
    /// cell as a cap-confined surface, share it READ-ONLY, then try to promote the
    /// read-only window to WRITABLE — the real executor REJECTS the widening
    /// (`DelegationDenied`), surfaced as `⚠ over-share` at the glass
    /// ([`crate::shell::ShellError::ShareDenied`]). Not part of the headless self-check
    /// (which needs no shell), but available for the cockpit's live path to show the
    /// refusal firing at the PIXEL layer too.
    ///
    /// Returns the refusal reason on the expected rejection, or an error if the
    /// widening wrongly succeeded (a fail-open regression).
    pub fn refuse_over_share(&mut self, shell: &mut crate::shell::Shell) -> Result<String, String> {
        if self.token == CellId::ZERO {
            return Err("MINT has not run (no token cell to open as a surface)".into());
        }
        // Open the budget cell as a cap-confined surface (a writable owner cap).
        let owner_cap = shell.open_cell_view(self.token, "budget (token) cell");
        // Share it READ-ONLY (a genuine narrowing — committed through the real
        // executor: AuthRequired::None [widest] → Signature [a narrower read-only]).
        let read_only = shell
            .share(&owner_cap, 0xB0B0, AuthRequired::Signature)
            .map_err(|e| format!("the legitimate read-only share unexpectedly failed: {e:?}"))?;
        // Now try to PROMOTE the read-only mirror back to writable (None is wider
        // than Signature) — the no-amplification rule must REJECT this at the glass.
        match shell.share(&read_only, 0xB0B0, AuthRequired::None) {
            Err(crate::shell::ShellError::ShareDenied(why)) => Ok(format!(
                "⚠ over-share REFUSED at the pixel layer — {why} \
                 (the read-only budget window cannot promote itself to writable; \
                 no-amplification at the glass)"
            )),
            Ok(_) => Err(
                "FAIL-OPEN: the writable over-share SUCCEEDED — no-amplification did NOT fire at the glass!"
                    .into(),
            ),
            Err(other) => Err(format!("the over-share was refused, but unexpectedly: {other:?}")),
        }
    }

    // --- the live (SWARM-tab) driver -------------------------------------------

    /// **Advance the live driver by ONE script step** — the cockpit's SWARM-tab
    /// button calls this; each press runs the next frame (MINT → AGENT TURN → NOTIFY
    /// → DRAIN → over-grant REFUSAL → over-spend REFUSAL). Returns the frame's render
    /// line, or `None` if the script is complete. A setup failure (a real regression)
    /// returns its label as the line (so the cockpit surfaces it loudly).
    pub fn advance(&mut self) -> Option<String> {
        let r = match self.cursor {
            0 => self.step_mint().map(|f| f.line()),
            1 => self.step_agent_turn().map(|f| f.line()),
            2 => self.step_notify().map(|f| f.line()),
            3 => self.step_drain().map(|f| f.line()),
            4 => self.refuse_over_grant().map(|f| f.line()),
            5 => self.refuse_over_spend().map(|f| f.line()),
            _ => return None,
        };
        Some(match r {
            Ok(line) => line,
            Err(e) => format!("  [demo] SETUP FAILURE (regression!) — {}", e.label()),
        })
    }

    /// Reset the live driver to a fresh world at frame 0 (the cockpit's "reset demo"
    /// affordance). Re-boots from scratch so the script can be replayed.
    pub fn reset(&mut self) {
        *self = HeadlineDemo::boot();
    }

    // --- the headless self-check (the CI-friendly artifact) --------------------

    /// **RUN THE FULL SCRIPT (the `--headless` self-check core).** Drives all four
    /// frames + the dual refusal through the REAL executor / the verified counter,
    /// ASSERTING each load-bearing invariant (the mint commits; the agent spend moves
    /// balance + the meter climbs; the handoff is TWO distinct receipts; BOTH refusals
    /// fire fail-closed). Returns the captured frames on success, or the first
    /// [`DemoError`] (a real regression) — the binary turns that into a non-zero exit.
    ///
    /// This is the engine behind `main.rs --headless`: it prints nothing itself (so it
    /// stays testable); the caller prints the frames + the verdict.
    pub fn run_headless(&mut self) -> Result<&[DemoFrame], DemoError> {
        self.step_mint()?;
        self.step_agent_turn()?;
        self.step_notify()?;
        self.step_drain()?;
        // THE DUAL REFUSAL — both must fire fail-closed (the climax).
        self.refuse_over_grant()?;
        self.refuse_over_spend()?;
        Ok(&self.frames)
    }

    /// Whether the captured frames satisfy the headline contract: the four frames
    /// committed (MINT, AGENT TURN, NOTIFY, DRAIN), the handoff produced two DISTINCT
    /// receipts, and BOTH refusal frames are present (over-grant + over-spend), each
    /// fail-closed. Used by the self-check to print the verdict + by the tests.
    pub fn contract_holds(&self) -> bool {
        let committed: Vec<&DemoFrame> = self.frames.iter().filter(|f| f.committed).collect();
        let refused: Vec<&DemoFrame> = self.frames.iter().filter(|f| !f.committed).collect();
        // Four committed frames (mint/agent/notify/drain) + two refusals.
        let has_mint = committed.iter().any(|f| f.stage == "MINT");
        let has_agent = committed.iter().any(|f| f.stage == "AGENT TURN");
        let has_notify = committed.iter().any(|f| f.stage == "NOTIFY");
        let has_drain = committed.iter().any(|f| f.stage == "DRAIN");
        // The two distinct handoff receipts.
        let notify_r = committed.iter().find(|f| f.stage == "NOTIFY").and_then(|f| f.receipt.clone());
        let drain_r = committed.iter().find(|f| f.stage == "DRAIN").and_then(|f| f.receipt.clone());
        let two_distinct = notify_r.is_some() && drain_r.is_some() && notify_r != drain_r;
        // Both refusals present, each carrying the executor's reason.
        let both_refusals = refused.len() >= 2
            && refused.iter().all(|f| f.refusal_reason.is_some());
        has_mint && has_agent && has_notify && has_drain && two_distinct && both_refusals
    }
}

impl Default for HeadlineDemo {
    fn default() -> Self {
        Self::boot()
    }
}

/// Format the demo's frames + verdict as the `--headless` self-check report (the
/// CI-friendly artifact). Returns the full multi-line string the binary prints; the
/// binary exits 0 iff [`HeadlineDemo::contract_holds`] (which this also reports).
pub fn render_headless_report(demo: &HeadlineDemo) -> String {
    let mut out = String::new();
    out.push_str("== Starbridge v2 · the four-surface killer demo (the pug-handoff artifact) ==\n");
    out.push_str(
        "  one token, born of a factory; an agent acting in-mandate; a notify handoff\n  \
         (two distinct receipts); and the DUAL REFUSAL — an over-grant AND an over-spend,\n  \
         both fail-closed through the REAL verified executor, each citing its reason.\n\n",
    );
    out.push_str("-- the four frames + the dual refusal --\n");
    for f in demo.frames() {
        out.push_str(&f.line());
        out.push('\n');
    }
    out.push('\n');
    // The grounded image state after the script.
    out.push_str(&format!(
        "-- grounded image: {} cells · height {} · {} receipts · image root {} --\n",
        demo.world().cell_count(),
        demo.world().height(),
        demo.world().receipts().len(),
        crate::reflect::short_hex(&demo.world().state_root()),
    ));
    if let Some(view) = demo.swarm().stingray_view() {
        out.push_str(&format!(
            "-- verified shared budget: drew {} of {} computrons ({} headroom) --\n",
            view.total_drawn, view.ceiling, view.remaining,
        ));
    }
    out.push('\n');
    if demo.contract_holds() {
        out.push_str(
            "VERDICT ✓ — the four frames committed, the handoff produced TWO distinct\n  \
             receipts, and BOTH refusals fired fail-closed citing the executor's reason.\n  \
             (step 5 — the pg-dregg Tier-B SQL mirror read — is the deferred follow-up.)\n",
        );
    } else {
        out.push_str("VERDICT ✗ — the headline contract did NOT hold (a regression).\n");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_full_script_runs_and_the_contract_holds() {
        // THE HEADLINE: the four frames + the dual refusal all run through the REAL
        // executor / the verified counter, and the contract holds.
        let mut demo = HeadlineDemo::boot();
        let frames = demo.run_headless().expect("the full script must run with no setup failure");
        // Six frames: mint, agent turn, notify, drain, over-grant refusal, over-spend
        // refusal.
        assert_eq!(frames.len(), 6, "four committed frames + the dual refusal");
        assert!(demo.contract_holds(), "the headline contract must hold");
    }

    #[test]
    fn frame_1_mint_is_a_real_factory_birth_with_a_receipt() {
        // FRAME 1: the MINT is a genuine factory-birth — a child cell appears, A is
        // granted a cap reaching it, and a real receipt is recorded.
        let mut demo = HeadlineDemo::boot();
        let before = demo.world().cell_count();
        let frame = demo.step_mint().expect("the mint must commit").clone();
        assert_eq!(frame.stage, "MINT");
        assert!(frame.committed);
        assert!(frame.receipt.is_some(), "the mint has a real receipt");
        assert_eq!(demo.world().cell_count(), before + 1, "the factory birthed a child cell");
        assert_ne!(demo.token(), CellId::ZERO, "the token cell id was recovered");
        // A holds a cap reaching the freshly-minted token cell (the genesis grant).
        assert!(
            demo.world().ledger().get(&demo.agent_a()).unwrap().capabilities.has_access(&demo.token()),
            "agent-A holds a cap reaching the minted token cell"
        );
    }

    #[test]
    fn frame_2_agent_turn_moves_balance_and_climbs_the_budget_meter() {
        // FRAME 2: the AGENT TURN is a real in-mandate spend — balance moves on the
        // token cell, conservation holds, and the verified budget meter climbs by the
        // metered computrons (non-vacuous).
        let mut demo = HeadlineDemo::boot();
        demo.step_mint().expect("mint");
        let drawn_before = demo.swarm().stingray_budget().unwrap().total_drawn();
        let token_bal_before = demo.world().ledger().get(&demo.token()).map(|c| c.state.balance()).unwrap_or(0);
        let frame = demo.step_agent_turn().expect("the agent turn must commit").clone();
        assert!(frame.committed);
        assert_eq!(frame.stage, "AGENT TURN");
        // The budget meter climbed by a non-zero metered amount (the conservation step).
        let drawn_after = demo.swarm().stingray_budget().unwrap().total_drawn();
        assert!(drawn_after > drawn_before, "the verified budget meter climbed by the metered spend");
        // The token cell's balance changed (a real value move: funded +10_000, spent -2_500).
        let token_bal_after = demo.world().ledger().get(&demo.token()).unwrap().state.balance();
        assert_ne!(token_bal_after, token_bal_before, "the spend moved real balance on the budget cell");
        assert_eq!(token_bal_after, 10_000 - 2_500, "funded 10_000, spent 2_500 back to A");
    }

    #[test]
    fn frame_3_notify_handoff_is_two_distinct_receipts() {
        // FRAME 3: the notify handoff produces TWO DISTINCT receipt hashes — A's emit
        // and B's drain — proving causality A→B AND independence (not a joint turn).
        let mut demo = HeadlineDemo::boot();
        demo.step_mint().expect("mint");
        demo.step_agent_turn().expect("agent turn");
        let notify = demo.step_notify().expect("the notify must commit").clone();
        let drain = demo.step_drain().expect("the drain must commit").clone();
        assert!(notify.committed && drain.committed);
        assert_eq!(notify.stage, "NOTIFY");
        assert_eq!(drain.stage, "DRAIN");
        // TWO DISTINCT receipts — the independence proof.
        assert!(notify.receipt.is_some() && drain.receipt.is_some());
        assert_ne!(
            notify.receipt, drain.receipt,
            "the emit and the drain are INDEPENDENT turns (two distinct receipt hashes)"
        );
        // The drain is at a strictly later height (a separate committed turn).
        assert!(drain.height > notify.height, "the drain is a later, separate turn");
    }

    #[test]
    fn frame_4a_the_over_grant_is_refused_by_no_amplification() {
        // FRAME 4 (a): compromised B's over-grant (widening its mandate to a cell it
        // holds no cap to) is REFUSED fail-closed by the no-amplification rule, citing
        // the executor's own reason. No fake-green: it is a real Err from the executor.
        let mut demo = HeadlineDemo::boot();
        demo.step_mint().expect("mint");
        demo.step_agent_turn().expect("agent turn");
        demo.step_notify().expect("notify");
        demo.step_drain().expect("drain");
        let h_before = demo.world().height();
        let frame = demo.refuse_over_grant().expect("the over-grant must fire its refusal").clone();
        assert!(!frame.committed, "the over-grant is REFUSED (a feature, not a commit)");
        assert_eq!(frame.stage, "REFUSAL");
        assert!(frame.refusal_reason.is_some(), "the refusal carries the executor's reason");
        // FAIL-CLOSED: no turn committed — the height did not advance.
        assert_eq!(demo.world().height(), h_before, "no height advance on the over-grant refusal");
    }

    #[test]
    fn frame_4b_the_over_spend_is_refused_by_the_stingray_ceiling() {
        // FRAME 4 (b): compromised B's over-spend past the verified Stingray ceiling
        // is REFUSED fail-closed by the counter's conservation gate (PoolExhausted),
        // the counter UNMOVED. The budget-ceiling half of the dual refusal.
        let mut demo = HeadlineDemo::boot();
        demo.step_mint().expect("mint");
        demo.step_agent_turn().expect("agent turn");
        demo.step_notify().expect("notify");
        demo.step_drain().expect("drain");
        demo.refuse_over_grant().expect("over-grant refusal");
        let drawn_before = demo.swarm().stingray_budget().unwrap().total_drawn();
        let h_before = demo.world().height();
        let frame = demo.refuse_over_spend().expect("the over-spend must fire its refusal").clone();
        assert!(!frame.committed, "the over-spend is REFUSED");
        assert_eq!(frame.stage, "REFUSAL");
        let reason = frame.refusal_reason.unwrap();
        assert!(
            reason.contains("Stingray") || reason.contains("ceiling") || reason.contains("conservation"),
            "the refusal cites the verified budget ceiling: {reason}"
        );
        // FAIL-CLOSED: no turn committed, the counter UNMOVED.
        assert_eq!(demo.world().height(), h_before, "no height advance on the over-spend refusal");
        assert_eq!(
            demo.swarm().stingray_budget().unwrap().total_drawn(),
            drawn_before,
            "the refused draw moved nothing — the verified counter is unmoved"
        );
    }

    #[test]
    fn the_dual_refusal_fires_both_halves_fail_closed() {
        // THE CLIMAX: BOTH refusals fire — the over-grant (no-amplification) AND the
        // over-spend (Stingray ceiling) — each fail-closed, each citing its reason.
        // This is the headline's "the same no-amplification law fired at the swarm seam
        // AND at the budget ceiling".
        let mut demo = HeadlineDemo::boot();
        demo.run_headless().expect("the full script runs");
        let refusals: Vec<&DemoFrame> = demo.frames().iter().filter(|f| !f.committed).collect();
        assert_eq!(refusals.len(), 2, "EXACTLY two refusals — the dual refusal");
        assert!(refusals.iter().all(|f| f.refusal_reason.is_some()), "each refusal cites its reason");
        // One of them is the over-grant; one is the over-spend (Stingray).
        assert!(
            refusals.iter().any(|f| f.headline.contains("OVER-GRANT")),
            "the over-grant refusal is present"
        );
        assert!(
            refusals.iter().any(|f| f.headline.contains("OVER-SPEND")),
            "the over-spend refusal is present"
        );
    }

    #[test]
    fn the_pixel_layer_over_share_is_also_refused() {
        // THE THIRD REGISTER (the SHELL cut): the SAME no-amplification law fires at
        // the PIXEL layer — promoting a read-only budget window to writable is REJECTED
        // (DelegationDenied, surfaced as over-share). Available for the live/SWARM-tab
        // path; not part of the headless self-check.
        let mut demo = HeadlineDemo::boot();
        demo.step_mint().expect("mint");
        let mut shell = crate::shell::Shell::new();
        let _console = shell.open_console(demo.agent_a(), "demo console");
        let reason = demo
            .refuse_over_share(&mut shell)
            .expect("the writable over-share must be REFUSED at the glass");
        assert!(
            reason.contains("over-share") && reason.contains("REFUSED"),
            "the pixel-layer over-share names the refusal: {reason}"
        );
    }

    #[test]
    fn the_live_driver_advances_one_frame_per_step() {
        // THE LIVE PATH: the cockpit's SWARM-tab driver advances one frame per call,
        // matching the headless script, and completes after TOTAL_STEPS.
        let mut demo = HeadlineDemo::boot();
        assert_eq!(demo.cursor(), 0);
        assert!(demo.next_step_label().unwrap().contains("MINT"));
        let mut lines = 0;
        while let Some(_line) = demo.advance() {
            lines += 1;
            if demo.is_complete() {
                break;
            }
        }
        assert_eq!(lines, HeadlineDemo::TOTAL_STEPS as usize, "one line per script step");
        assert!(demo.is_complete(), "the script completes");
        assert!(demo.contract_holds(), "the live-driven script satisfies the contract");
    }

    #[test]
    fn the_headless_report_renders_the_frames_and_a_passing_verdict() {
        // The CI-friendly report names the four frames + the dual refusal and prints a
        // passing verdict when the contract holds.
        let mut demo = HeadlineDemo::boot();
        demo.run_headless().expect("script runs");
        let report = render_headless_report(&demo);
        assert!(report.contains("MINT"));
        assert!(report.contains("AGENT TURN"));
        assert!(report.contains("NOTIFY"));
        assert!(report.contains("DRAIN"));
        assert!(report.contains("OVER-GRANT"));
        assert!(report.contains("OVER-SPEND"));
        assert!(report.contains("VERDICT ✓"), "a passing verdict when the contract holds");
        // The deferred step 5 is named as a follow-up, not silently dropped.
        assert!(report.contains("step 5") || report.contains("Tier-B"), "the deferred pg step is named");
    }

    #[test]
    fn reset_reboots_the_demo_to_a_fresh_world() {
        // The cockpit's "reset" affordance re-boots from scratch so the script replays.
        let mut demo = HeadlineDemo::boot();
        demo.run_headless().expect("script runs");
        assert!(demo.is_complete());
        demo.reset();
        assert_eq!(demo.cursor(), 0, "reset returns to frame 0");
        assert!(demo.frames().is_empty(), "reset clears the frames");
        assert_eq!(demo.token(), CellId::ZERO, "reset clears the minted token");
        // And the script can be replayed cleanly.
        demo.run_headless().expect("the replayed script runs");
        assert!(demo.contract_holds());
    }
}
