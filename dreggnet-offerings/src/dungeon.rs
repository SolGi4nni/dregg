//! **Offering #0 — the dungeon.** The `discord-bot/fiction.rs` `RealSession` logic, factored
//! out of the Discord frontend into a [`DungeonOffering`] that implements the frontend-agnostic
//! [`Offering`] trait over `dungeon_on_dregg`'s real `WorldCell`.
//!
//! What was Discord-coupled in `fiction.rs` (serenity embeds, ballot buttons, the round/tally,
//! the narrator gate) splits cleanly:
//! - the **substrate seam** — deploy the Keep, run genesis, apply a choice as ONE real
//!   cap-bounded turn, record the [`Playthrough`], re-verify by replay — is THIS module (the
//!   [`DungeonSession`] is the old `RealSession`, verbatim in substance).
//! - the **ballot / tally / plurality** is the *orchestrator's* job (collective-choice); the
//!   core resolves the single typed [`Action`] the crowd picked.
//! - the **embed / buttons** is the *frontend's* job; the core renders a deos [`Surface`].
//! - the **narrator credit gate** is the *frontend's* job; the core names the [`RunCost`].
//!
//! The executor is the SOURCE OF TRUTH: a legal move lands a real `TurnReceipt`; an illegal one
//! (a killing blow past the HP floor, a second grab of a `WriteOnce` relic, climbing a one-way
//! stair, an over-budget ward) is a real `WorldError::Refused` that commits nothing — the
//! anti-ghost tooth. `verify` re-drives a fresh identically-seeded world-cell through the
//! recorded choices ([`verify_by_replay`]); a forged/reordered record fails.

use deos_view::{MenuItem, ViewNode};
use dregg_app_framework::TurnReceipt;
use spween::{CompareOp, ConditionClause, ConditionExpr, PassageContent, Scene};
use spween_dregg::{StepReceipt, WorldCell, WorldError, value_to_u64, verify, verify_by_replay};

use dungeon_on_dregg::{deploy_keep, keep_scene};

use crate::{
    Action, CollectiveDecision, DreggIdentity, Offering, OfferingError, Outcome, RecordVerify,
    RunCost, SessionConfig, Surface, VerifyReport,
};

/// Re-export of the substrate **playthrough** — the public, transmissible session record the
/// [`RecordVerify`] tamper-verify seam exports and re-checks. Re-exported here so a frontend can
/// name the record type (and forge a copy in a tamper test) without depending on `spween-dregg`
/// directly.
pub use spween_dregg::{Playthrough, VerifyBreak};

/// The affordance verb every dungeon move fires — a choice on the current room's ballot. The
/// action's `arg` is the scene choice index within the current passage.
pub const TURN_CHOOSE: &str = "choose";

/// The hosted universe's display name.
pub const KEEP_NAME: &str = "The Warden's Keep";

/// The Keep's objective, stated for the party.
pub const KEEP_OBJECTIVE: &str = "trade past the gate-warden, claim the crown, descend the collapsing stair, and seize the hoard";

/// **A dungeon play session over the REAL substrate** — the factored `fiction.rs` `RealSession`.
/// Owns the live [`WorldCell`] (the committed dungeon-on-dregg Keep), the owned scene (the
/// choices/conditions actions are built from), the deterministic seed, and the accumulated
/// [`Playthrough`] (genesis + committed steps) that [`DungeonOffering::verify`] re-verifies by
/// replay. Also keeps a per-step **actor log** (who drove each move) — session metadata beside
/// the world-signed substrate turn, so a frontend can attribute moves without the executor
/// (which signs with the world's cap) having to.
pub struct DungeonSession {
    /// The live world-cell — genesis committed, subsequent moves committed on it.
    world: WorldCell,
    /// The owned Keep scene (deterministic; a re-deploy under `seed` reproduces it).
    scene: Scene,
    /// The deterministic deploy seed — `verify` re-deploys a fresh identically-seeded cell.
    seed: u8,
    /// The genesis receipt (intro entry effects + initial passage bind).
    genesis: TurnReceipt,
    /// The committed slot vector right after genesis (the replay verifier reproduces it).
    genesis_state: Vec<u64>,
    /// The committed choice-steps, in order — each a real landed turn.
    steps: Vec<StepReceipt>,
    /// Who drove each committed step (parallel to `steps`) — session-level attribution. For a
    /// collective turn this is the decision's *carrier* (the mover of record).
    actors: Vec<DreggIdentity>,
    /// The collective decision behind each committed step (parallel to `steps`): `None` for a
    /// single-actor [`Offering::advance`], `Some` for an [`Offering::advance_collective`] crowd
    /// turn — the recorded electorate + carrier + tally, the crowd decision made first-class.
    collectives: Vec<Option<CollectiveDecision>>,
}

impl DungeonSession {
    /// The current passage name (the "room"), if the dungeon is still running.
    pub fn current_passage_name(&self) -> Option<String> {
        let idx = self.world.read_passage()?;
        self.scene.passages.get(idx).map(|p| p.name.to_string())
    }

    /// The current room's prose (the scene's authored description of the passage).
    pub fn current_prose(&self) -> String {
        let Some(idx) = self.world.read_passage() else {
            return String::new();
        };
        let Some(passage) = self.scene.passages.get(idx) else {
            return String::new();
        };
        let mut out = String::new();
        for c in &passage.content {
            if let PassageContent::Prose(p) = c {
                if !out.is_empty() {
                    out.push(' ');
                }
                out.push_str(p.text.trim());
            }
        }
        out
    }

    /// Whether the dungeon has ended.
    pub fn is_ended(&self) -> bool {
        self.world.read_passage().is_none()
    }

    /// The number of real verified turns so far (genesis + committed steps).
    pub fn receipts_len(&self) -> usize {
        1 + self.steps.len()
    }

    /// Read a narrative var off the committed cell state.
    pub fn read_var(&self, name: &str) -> u64 {
        self.world.read_var(name)
    }

    /// The recorded playthrough (genesis + committed steps) — the input to replay-verify.
    pub fn playthrough(&self) -> Playthrough {
        Playthrough {
            genesis: self.genesis.clone(),
            genesis_state: self.genesis_state.clone(),
            steps: self.steps.clone(),
        }
    }

    /// The actor who drove step `n` (0-based over committed steps), if recorded. For a collective
    /// step this is the decision's carrier (the mover of record).
    pub fn actor_of_step(&self, n: usize) -> Option<&DreggIdentity> {
        self.actors.get(n)
    }

    /// The [`CollectiveDecision`] behind step `n` (0-based over committed steps), if the step was
    /// a crowd turn ([`Offering::advance_collective`]). `None` for a single-actor step or an
    /// absent index — the recorded electorate + carrier + tally, the crowd decision first-class.
    pub fn collective_of_step(&self, n: usize) -> Option<&CollectiveDecision> {
        self.collectives.get(n).and_then(|c| c.as_ref())
    }

    /// A compact one-line projection of the party's committed state (for the surface).
    pub fn state_line(&self) -> String {
        let owner = match self.read_var("relic_owner") {
            1 => "Red Hand",
            2 => "Blue Hand",
            _ => "unclaimed",
        };
        format!(
            "HP {} · depth {} · gold {} · crown {} · will spent {}",
            self.read_var("hp"),
            self.read_var("depth"),
            self.read_var("gold"),
            owner,
            self.read_var("mana_spent"),
        )
    }
}

/// **The dungeon offering** — offering #0. A stateless factory over the hosted Keep universe;
/// each [`open`](Offering::open) deploys a fresh [`DungeonSession`]. Carries the per-move
/// [`RunCost`] (the free tier by default; a paid tier prices the confined narrator — which the
/// frontend, not the core, actually debits and runs).
pub struct DungeonOffering {
    /// Run-credits a move's paid narration costs (`0` → free tier). The substrate turn is
    /// always free + verifiable; this prices the confined intelligence overlay.
    narration_credits: u64,
}

impl DungeonOffering {
    /// The free-tier dungeon (no credit debited per move; scripted/local narration).
    pub fn new() -> Self {
        DungeonOffering {
            narration_credits: 0,
        }
    }

    /// A paid-tier dungeon: each move's hosted narration costs `credits` run-credits (the
    /// frontend debits them against the actor's `dregg_pay` balance before serving the render).
    pub fn paid(credits: u64) -> Self {
        DungeonOffering {
            narration_credits: credits,
        }
    }

    /// The current room's choices as cap-gated [`Action`]s (the ballot options / affordances),
    /// in the SAME order the compiler indexed them (so `arg` is exactly the choice index
    /// [`WorldCell::apply_choice`] checks the gate case against). A choice whose scene condition
    /// currently fails is `enabled: false` — the cap tooth shown, not hidden (a decoration; the
    /// executor is the sole referee — a gated illegal move still refuses on `advance`).
    fn room_actions(&self, session: &DungeonSession) -> Vec<Action> {
        let Some(idx) = session.world.read_passage() else {
            return Vec::new();
        };
        let Some(passage) = session.scene.passages.get(idx) else {
            return Vec::new();
        };
        passage
            .content
            .iter()
            .filter_map(|c| match c {
                PassageContent::Choice(ch) => Some(ch),
                _ => None,
            })
            .enumerate()
            .map(|(choice_index, choice)| {
                let available = choice
                    .condition
                    .as_ref()
                    .map(|c| eval_condition(&c.expr, &session.world))
                    .unwrap_or(true);
                Action::new(
                    choice.text.to_string(),
                    TURN_CHOOSE,
                    choice_index as i64,
                    available,
                )
            })
            .collect()
    }
}

impl Default for DungeonOffering {
    fn default() -> Self {
        DungeonOffering::new()
    }
}

impl Offering for DungeonOffering {
    type Session = DungeonSession;

    /// Deploy a fresh session hosting the Keep: deploy a real world-cell under the config seed,
    /// run the intro's entry effects as the genesis turn (via the stock [`Driver`], finished to
    /// hold the post-genesis cell), and record the genesis snapshot. (The factored
    /// `RealSession::open`.)
    fn open(&self, cfg: SessionConfig) -> Result<DungeonSession, OfferingError> {
        // A deterministic deploy seed in 1..=251 (stable per session → replay-verifiable
        // identity), derived from the config seed (default 1).
        let seed = ((cfg.seed.unwrap_or(1) % 251) + 1) as u8;
        let scene = keep_scene();
        let world = deploy_keep(seed);
        // Drive genesis with the stock runtime (intro entry effects: hp=50, mana_budget=50),
        // then finish to hold the post-genesis world-cell for direct `apply_choice` play.
        let driver = spween_dregg::Driver::start(world, &scene)
            .map_err(|e| OfferingError::Deploy(e.to_string()))?;
        let genesis = driver.genesis().cloned().unwrap_or_default();
        let genesis_state = driver.playthrough().genesis_state;
        let (world, _no_steps) = driver.finish();
        Ok(DungeonSession {
            world,
            scene,
            seed,
            genesis,
            genesis_state,
            steps: Vec::new(),
            actors: Vec::new(),
            collectives: Vec::new(),
        })
    }

    fn actions(&self, session: &DungeonSession) -> Vec<Action> {
        self.room_actions(session)
    }

    /// **Apply a choice as ONE real cap-bounded turn** (the factored `RealSession::apply_winner`
    /// + the anti-ghost tooth). `input.arg` is the scene choice index. A legal move commits a
    /// real [`TurnReceipt`] (recorded onto the playthrough + the actor log); an illegal / stale
    /// / forged one is a real [`WorldError::Refused`] — nothing commits, no step recorded.
    fn advance(
        &self,
        session: &mut DungeonSession,
        input: Action,
        actor: DreggIdentity,
    ) -> Outcome {
        if input.turn != TURN_CHOOSE {
            return Outcome::Refused(format!("unknown affordance: {}", input.turn));
        }
        if input.arg < 0 {
            return Outcome::Refused("that move is not on the current ballot".to_string());
        }
        let choice_index = input.arg as usize;

        let Some(idx) = session.world.read_passage() else {
            return Outcome::Refused("the dungeon has already ended".to_string());
        };
        let passage_name = match session.scene.passages.get(idx) {
            Some(p) => p.name.to_string(),
            None => return Outcome::Refused("no current passage".to_string()),
        };
        let Some(choice) = nth_choice(&session.scene, &passage_name, choice_index) else {
            return Outcome::Refused("that move is not on the current ballot".to_string());
        };

        match session
            .world
            .apply_choice(&passage_name, choice_index, &choice)
        {
            Ok(receipt) => {
                let step = StepReceipt {
                    passage: passage_name,
                    choice_index,
                    receipt: receipt.clone(),
                    state: session.world.snapshot(),
                };
                session.steps.push(step);
                session.actors.push(actor);
                // Keep the collective log parallel to `steps`; `advance` is single-actor, so no
                // crowd decision by default. `advance_collective` fills this slot after us.
                session.collectives.push(None);
                let ended = session.world.read_passage().is_none();
                Outcome::Landed { receipt, ended }
            }
            Err(WorldError::Refused(why)) => Outcome::Refused(why),
            Err(e) => Outcome::Refused(e.to_string()),
        }
    }

    /// **Record a first-class crowd turn** (the collective analogue of `advance`). Resolves the
    /// winning [`Action`] as ONE real cap-bounded turn attributed to the decision's `carrier`
    /// (via [`advance`](Self::advance) — the substrate still admits exactly one typed move), then,
    /// *iff it landed*, persists the whole [`CollectiveDecision`] (electorate + tally + carrier)
    /// beside the committed step. So the receipt says "the PARTY (these voters) decided X, carried
    /// by Y" with the real electorate — closing the gap where the /dungeon frontend attributed the
    /// crowd turn to a nameless `party_actor()` constant. A refused move records nothing (the
    /// anti-ghost tooth: no step, no decision).
    fn advance_collective(
        &self,
        session: &mut DungeonSession,
        input: Action,
        decision: CollectiveDecision,
    ) -> Outcome {
        let carrier = decision.carrier.clone();
        let out = self.advance(session, input, carrier);
        if out.landed() {
            // `advance` just pushed a `None` collective slot for this landed step; fill it with
            // the crowd decision (electorate + tally), making the crowd turn first-class.
            if let Some(slot) = session.collectives.last_mut() {
                *slot = Some(decision);
            }
        }
        out
    }

    /// **Re-verify the whole receipt chain by REPLAY** — re-drives a fresh identically-seeded
    /// world-cell through the recorded choices and confirms it reproduces exactly the committed
    /// state chain in passage order ([`verify_by_replay`]). A forged/reordered record fails.
    fn verify(&self, session: &DungeonSession) -> VerifyReport {
        let turns = session.receipts_len();
        match verify_by_replay(
            deploy_keep(session.seed),
            &session.scene,
            &session.playthrough(),
        ) {
            Ok(()) => VerifyReport::ok(turns),
            Err(b) => VerifyReport::broken(turns, b.to_string()),
        }
    }

    /// Render the current room as a **deos affordance [`Surface`]**: the room prose + the party
    /// state + verified-turn count, and the choices as a cap-gated affordance [`Menu`] (each row
    /// a `{turn: "choose", arg: choice_index}` affordance; an ineligible choice is a dimmed
    /// `!enabled` row — the cap tooth shown, not hidden).
    fn render(&self, session: &DungeonSession) -> Surface {
        let room_name = session
            .current_passage_name()
            .unwrap_or_else(|| "the dark".to_string());
        let actions = self.room_actions(session);

        let mut children = vec![
            ViewNode::Text(session.current_prose()),
            ViewNode::Section {
                title: "Party".to_string(),
                tag: "muted".to_string(),
                children: vec![ViewNode::Text(session.state_line())],
            },
            ViewNode::Section {
                title: "Objective".to_string(),
                tag: "muted".to_string(),
                children: vec![ViewNode::Text(KEEP_OBJECTIVE.to_string())],
            },
            ViewNode::Section {
                title: "Verified turns".to_string(),
                tag: "genuine".to_string(),
                children: vec![ViewNode::Text(session.receipts_len().to_string())],
            },
        ];

        if session.is_ended() {
            children.push(ViewNode::Section {
                title: "The Keep is cleared".to_string(),
                tag: "genuine".to_string(),
                children: vec![ViewNode::Text(
                    "The objective is met — one real turn at a time.".to_string(),
                )],
            });
        } else {
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
                title: "The party's move".to_string(),
                tag: "accent".to_string(),
                children: vec![ViewNode::Menu { items }],
            });
        }

        Surface(ViewNode::Section {
            title: format!("{KEEP_NAME} — {room_name}"),
            tag: "accent".to_string(),
            children,
        })
    }

    /// The move's [`RunCost`] — the free tier by default; the paid tier prices the confined
    /// narrator (which the frontend debits + runs). The substrate turn itself is always free.
    fn price(&self, _input: &Action) -> RunCost {
        RunCost::credits(self.narration_credits)
    }
}

/// **The frontend-facing tamper-verify seam for the dungeon.** A frontend holds a session
/// (opaquely) and its exported [`Playthrough`]; it can serialize/transmit the record and might
/// receive a **forged** copy back. [`verify_record`](RecordVerify::verify_record) re-checks any
/// such record against the session's authentic world identity (the private `seed`/`scene`) using
/// the FULL substrate verifier ([`verify`] — both teeth: chain-linkage + replay), so a frontend
/// can express "a forged record fails" without reaching substrate internals. Strictly stronger
/// than [`Offering::verify`] (which runs replay only): a spliced/relinked receipt that replay
/// alone might miss is still caught by the linkage tooth.
impl RecordVerify for DungeonOffering {
    type Session = DungeonSession;
    type Record = Playthrough;

    /// Export the session's authentic playthrough (genesis + committed steps) — the public record
    /// a frontend transmits / persists / re-checks. No private world identity leaves the offering.
    fn export_record(&self, session: &DungeonSession) -> Playthrough {
        session.playthrough()
    }

    /// Re-verify a (possibly forged) `record` against the session's authentic world identity —
    /// re-deploy a fresh identically-seeded Keep and run BOTH verification teeth over the record.
    /// A legal record re-verifies; a forged / reordered / ineligible / spliced one fails.
    fn verify_record(&self, session: &DungeonSession, record: &Playthrough) -> VerifyReport {
        let turns = record.receipts().len();
        match verify(deploy_keep(session.seed), &session.scene, record) {
            Ok(()) => VerifyReport::ok(turns),
            Err(b) => VerifyReport::broken(turns, b.to_string()),
        }
    }
}

/// Pull the `n`-th `Choice` out of `passage` in the scene (the same ordering the compiler
/// indexes with `choice_method(passage, n)`). `None` if the passage or index is absent — a
/// non-panicking lookup used when applying a possibly-stale ballot winner. (Factored verbatim
/// from `fiction.rs`.)
fn nth_choice(scene: &Scene, passage_name: &str, n: usize) -> Option<spween::Choice> {
    let passage = scene
        .passages
        .iter()
        .find(|p| p.name.as_str() == passage_name)?;
    passage
        .content
        .iter()
        .filter_map(|c| match c {
            PassageContent::Choice(ch) => Some(ch),
            _ => None,
        })
        .nth(n)
        .cloned()
}

/// Evaluate a scene condition against the committed cell state (mirrors the runtime's own
/// evaluation via the public world reads). Used only to decide an affordance's `enabled`
/// decoration; the installed `CellProgram` gate is the sole authority over whether a move lands.
fn eval_condition(expr: &ConditionExpr, world: &WorldCell) -> bool {
    match expr {
        ConditionExpr::Atom(clause) => eval_clause(clause, world),
        ConditionExpr::And(a, b) => eval_condition(a, world) && eval_condition(b, world),
        ConditionExpr::Or(a, b) => eval_condition(a, world) || eval_condition(b, world),
    }
}

fn eval_clause(clause: &ConditionClause, world: &WorldCell) -> bool {
    match clause {
        ConditionClause::Has(h) => world.read_membership(&h.category, &h.key),
        ConditionClause::Compare(c) => {
            let lhs = world.read_var(&c.var);
            let rhs = value_to_u64(&c.value);
            match c.op {
                CompareOp::Ge => lhs >= rhs,
                CompareOp::Le => lhs <= rhs,
                CompareOp::Gt => lhs > rhs,
                CompareOp::Lt => lhs < rhs,
                CompareOp::Eq => lhs == rhs,
                CompareOp::Ne => lhs != rhs,
            }
        }
        ConditionClause::Not(inner) => !eval_clause(inner, world),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The replay-tamper tooth — an in-crate test (it reaches the session's private
// `scene`/`seed` to forge the committed record, exactly as `fiction.rs`'s own
// forged-choice test does). The end-to-end driven flow (open → advance → verify →
// render → frontend) lives in `tests/driven.rs`.
// ─────────────────────────────────────────────────────────────────────────────
#[cfg(test)]
mod forge_tests {
    use super::*;
    use crate::SessionConfig;
    use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON};

    /// A legal line re-verifies by replay; then a FORGED committed record (the first step's
    /// choice swapped) fails replay — the executor refuses on re-drive, or the reproduced state
    /// diverges. The real receipt-chain tooth end to end, through the [`Offering`] API.
    #[test]
    fn a_forged_choice_fails_replay() {
        let off = DungeonOffering::new();
        let mut s = off
            .open(SessionConfig::with_seed(9))
            .expect("the Keep opens");
        let actor = DreggIdentity("party".to_string());

        assert!(
            off.advance(
                &mut s,
                Action::new("press on", TURN_CHOOSE, KP_PRESS_ON as i64, true),
                actor.clone(),
            )
            .landed()
        );
        assert!(
            off.advance(
                &mut s,
                Action::new("claim red", TURN_CHOOSE, KP_CLAIM_RED as i64, true),
                actor,
            )
            .landed()
        );
        assert!(off.verify(&s).verified, "the legal line re-verifies");

        // Forge the recorded record: gatehall had choices 0 (trade-blows) and 1 (press-on);
        // swap the first step's 1 → 0 and confirm replay rejects it.
        let mut play = s.playthrough();
        if let Some(first) = play.steps.first_mut() {
            first.choice_index = 0;
        }
        let out = verify_by_replay(deploy_keep(s.seed), &s.scene, &play);
        assert!(
            out.is_err(),
            "a forged choice must fail replay, got {out:?}"
        );
    }
}
