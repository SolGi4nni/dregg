//! The live WORKSPACE / EVALUATOR — the Smalltalk doIt / printIt / inspectIt loop,
//! dregg-native.
//!
//! Smalltalk's workspace is a scratch surface where you select an expression and
//! `doIt` (evaluate it), `printIt` (evaluate + show the printed result inline), or
//! `inspectIt` (evaluate + open the result as a live, navigable object). This
//! module is that loop for dregg — a place to compose a TURN, EVALUATE it against
//! the live image *without committing* (fork-the-world predict-before-commit), see
//! the predicted result, inspect the predicted post-state as a live reflective
//! object, and only then COMMIT it (a verified turn, a real receipt) or DISCARD it
//! (the fork dropped, the world untouched).
//!
//! It REUSES the real heart, never a parallel model:
//!   * the composed expression IS [`crate::simulate::IntentDraft`] — the same draft
//!     shape the SIMULATE composer drives (the `world` verbs lowered to real
//!     `dregg_turn::Effect`s); this module invents NO new turn type.
//!   * **evaluate / doIt** = [`crate::simulate::simulate`] — the fork-the-world
//!     predict engine. It deep-clones the live ledger into a throwaway [`World`]
//!     running the SAME verified executor and runs the turn there, so the live
//!     world is NEVER mutated and the prediction is the live executor's own verdict
//!     run one turn ahead.
//!   * **printIt** = a concise predicted RESULT/receipt summary (the printed value
//!     of the evaluation — a one-line receipt the way `printIt` shows a result).
//!   * **inspectIt** = the predicted POST-STATE projected through
//!     [`crate::reflect::Inspectable`] — the touched cells + the image, as the SAME
//!     uniform reflective objects every cockpit view consumes, but read off the
//!     FORK's post-state so you inspect the predicted world before it is real.
//!   * **commit** = [`crate::simulate::commit`] → the real [`World::commit_turn`]:
//!     the IDENTICAL turn the prediction previewed, now on the live world (a real
//!     receipt that matches the prediction). **discard** drops the evaluation; the
//!     world is untouched.
//!
//! gpui-free + `cargo test`-able: this is the evaluator MODEL; a cockpit WORKSPACE
//! tab is a thin view over it (it renders exactly these rows). Like
//! [`crate::simulate`] / [`crate::landing`], the content is pure data, so the tests
//! below prove the doIt/printIt/inspectIt/commit/discard loop without a GPU.

use crate::reflect::{self, Inspectable};
use crate::simulate::{self, IntentDraft, SimOutcome};
use crate::world::{CommitOutcome, World};

// ===========================================================================
// THE EVALUATION — the result of a doIt (an evaluated, not-yet-committed turn).
// ===========================================================================

/// The result of EVALUATING the workspace's composed turn against the live image
/// — a `doIt` that ran the turn in a fork and predicted its consequences WITHOUT
/// committing. Carries the live executor's verdict ([`SimOutcome`]) plus the
/// predicted post-state projected as live reflective objects (the `inspectIt`
/// surface). The live world is untouched; this is a what-if you can print, inspect,
/// and then commit or discard.
pub struct Evaluation {
    /// The draft that was evaluated (the composed expression). Retained so a later
    /// [`Workspace::commit`] runs the SAME turn the prediction previewed.
    draft: IntentDraft,
    /// The live executor's verdict, run one turn ahead on a throwaway fork: either
    /// the predicted receipt + per-cell deltas, or the refusal reason. The live
    /// world was NOT mutated to produce it.
    pub outcome: SimOutcome,
    /// The predicted post-state, projected through [`reflect::Inspectable`]: the
    /// image object first, then one object per cell the turn TOUCHED (read off the
    /// fork's post-state). Empty when the evaluation refused (no post-state to
    /// inspect — the turn never committed, even in the fork). This is the
    /// `inspectIt` surface — the live, navigable predicted objects.
    pub inspected: Vec<Inspectable>,
}

impl Evaluation {
    /// `true` iff the evaluation predicts the turn WOULD commit (a `doIt` that the
    /// executor accepted in the fork). Only then may [`Workspace::commit`] run.
    pub fn would_commit(&self) -> bool {
        self.outcome.would_commit()
    }

    /// The draft this evaluation previewed (the expression that was evaluated).
    pub fn draft(&self) -> &IntentDraft {
        &self.draft
    }

    /// **printIt** — the concise printed RESULT of the evaluation (one line, the
    /// way Smalltalk's `printIt` shows a result inline). For a predicted commit:
    /// the predicted receipt hash + action/computron counts + the predicted image
    /// root + the net cell-count change. For a refusal: the executor's reason
    /// (truncated), prefixed so the printed value reads as the refusal it is.
    ///
    /// Distinct from [`simulate::render_outcome`] (the multi-line SIMULATE PANEL):
    /// this is the single-line printed *value* of the doIt, for an inline workspace
    /// echo. Both read the SAME [`SimOutcome`]; neither re-runs the executor.
    pub fn print_it(&self) -> String {
        match &self.outcome {
            SimOutcome::Predicted {
                receipt,
                cell_count_delta,
                predicted_root,
                ..
            } => {
                let mut s = format!(
                    "⇒ receipt {} · {} action(s) · {} computrons · root {}",
                    reflect::short_hex(&receipt.receipt_hash()),
                    receipt.action_count,
                    receipt.computrons_used,
                    reflect::short_hex(predicted_root),
                );
                if *cell_count_delta != 0 {
                    s.push_str(&format!(" · cells {cell_count_delta:+}"));
                }
                s
            }
            SimOutcome::Refused { reason, static_refusal, .. } => {
                let gate = if *static_refusal { "static rail" } else { "executor" };
                format!("⇒ REFUSED ({gate}): {}", truncate(reason, 160))
            }
        }
    }

    /// **inspectIt** — the predicted post-state as live reflective objects (the
    /// SAME [`reflect::Inspectable`] tree every cockpit inspector renders). The
    /// image object first, then the cells the turn touched, read off the predicted
    /// post-state. Empty if the turn refused (nothing committed to inspect).
    pub fn inspect_it(&self) -> &[Inspectable] {
        &self.inspected
    }
}

/// Truncate `s` to at most `max` chars (UTF-8-safe), appending `…` if cut.
fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        s.to_string()
    } else {
        let cut: String = s.chars().take(max).collect();
        format!("{cut}…")
    }
}

// ===========================================================================
// THE WORKSPACE — the live evaluator over a borrowed World.
// ===========================================================================

/// The live workspace / evaluator: a draft you compose, evaluate (`doIt` — predict
/// without committing), print (`printIt`), inspect (`inspectIt`), then commit or
/// discard — all against a live [`World`].
///
/// The workspace holds the in-progress [`IntentDraft`] and the most recent
/// [`Evaluation`]. It NEVER owns the world (so it can't drift from the live image):
/// [`Self::evaluate`] borrows it `&` (the fork is its own throwaway copy — the live
/// world is untouched), and [`Self::commit`] borrows it `&mut` only at the moment
/// the operator commits. Evaluating again, editing the draft, or [`Self::discard`]
/// all leave the live world exactly as it was — only `commit` advances it.
pub struct Workspace {
    /// The composed expression (the draft turn). Built incrementally (pick the
    /// agent, add actions, add effects) exactly as the SIMULATE composer does —
    /// this reuses [`IntentDraft`], it does not wrap a parallel builder.
    draft: IntentDraft,
    /// The most recent evaluation (a `doIt` result), or `None` before the first
    /// evaluate / after a [`Self::discard`].
    last: Option<Evaluation>,
}

impl Workspace {
    /// A fresh workspace whose draft is authored by `agent` (no actions yet).
    pub fn new(agent: dregg_cell::CellId) -> Self {
        Workspace { draft: IntentDraft::new(agent), last: None }
    }

    /// A workspace seeded with an already-composed `draft` (e.g. lifted from the
    /// SIMULATE composer — the SAME draft type, so no translation).
    pub fn with_draft(draft: IntentDraft) -> Self {
        Workspace { draft, last: None }
    }

    /// The composed expression, for the composer to mutate (add/remove actions and
    /// effects). Mutating it does NOT invalidate `last` automatically — the
    /// operator re-runs [`Self::evaluate`] to refresh the prediction (so a stale
    /// evaluation is visibly stale until re-run, never silently wrong: `commit`
    /// always rebuilds the turn from the CURRENT draft).
    pub fn draft_mut(&mut self) -> &mut IntentDraft {
        &mut self.draft
    }

    /// The composed expression (read).
    pub fn draft(&self) -> &IntentDraft {
        &self.draft
    }

    /// The most recent evaluation, if any.
    pub fn last(&self) -> Option<&Evaluation> {
        self.last.as_ref()
    }

    /// **doIt** — EVALUATE the composed turn against the live `world`, predicting
    /// its consequences WITHOUT committing.
    ///
    /// Runs [`simulate::simulate`] (fork-the-world: the turn runs on a deep copy of
    /// the live ledger through the SAME verified executor — the live `world` is `&`,
    /// never mutated), then projects the predicted POST-STATE as reflective objects
    /// (the `inspectIt` surface) by re-running the SAME turn on a second fork and
    /// reading back the touched cells + the image. Stores + returns the
    /// [`Evaluation`]. The live world is untouched.
    pub fn evaluate(&mut self, world: &World) -> &Evaluation {
        let outcome = simulate::simulate(world, &self.draft);
        let inspected = match &outcome {
            SimOutcome::Predicted { deltas, .. } => {
                // Re-fork and run the SAME turn to read the predicted post-state as
                // live objects. The fork is a throwaway deep copy on the SAME
                // executor (the live world is untouched); the turn is byte-identical
                // to the one `simulate` previewed and `commit` will run, so the
                // inspected post-state is exactly the predicted one.
                let mut fork = world.fork();
                let turn = self.draft.build_turn(world);
                let mut objs: Vec<Inspectable> = Vec::new();
                if fork.commit_turn(turn).is_committed() {
                    // The image object first (the predicted whole-image commitment).
                    objs.push(reflect::reflect_image(&fork));
                    // Then each touched cell, in the deltas' order, as it stands in
                    // the predicted post-state (skip retirements — nothing to show).
                    for d in deltas {
                        if let Some(cell) = fork.ledger().get(&d.cell) {
                            objs.push(reflect::reflect_cell(&d.cell, cell));
                        }
                    }
                }
                objs
            }
            // A refusal has no committed post-state to inspect.
            SimOutcome::Refused { .. } => Vec::new(),
        };
        self.last = Some(Evaluation { draft: self.draft.clone(), outcome, inspected });
        self.last.as_ref().expect("just set")
    }

    /// **printIt** of the last evaluation (convenience). `None` if nothing has been
    /// evaluated yet.
    pub fn print_it(&self) -> Option<String> {
        self.last.as_ref().map(Evaluation::print_it)
    }

    /// **inspectIt** of the last evaluation (convenience): the predicted post-state
    /// objects. Empty slice if nothing evaluated or the last evaluation refused.
    pub fn inspect_it(&self) -> &[Inspectable] {
        self.last.as_ref().map(Evaluation::inspect_it).unwrap_or(&[])
    }

    /// **COMMIT** — run the IDENTICAL turn the last evaluation previewed on the LIVE
    /// `world`, mutating it for real (the verified turn, the real receipt).
    ///
    /// Only valid when the last evaluation predicted a commit ([`Self::can_commit`]);
    /// returns `None` otherwise (no evaluation, or the prediction refused) so the
    /// caller can't commit a turn the executor would reject. On commit the live
    /// world advances (a real [`CommitOutcome::Committed`] whose receipt matches the
    /// prediction) and the evaluation is CLEARED (it described the pre-commit fork;
    /// the operator re-evaluates against the now-advanced world for the next step).
    ///
    /// The turn is rebuilt from the draft the evaluation captured (not the live
    /// `draft`), so an edit made after evaluating cannot silently change what
    /// commits — what you previewed is what commits.
    pub fn commit(&mut self, world: &mut World) -> Option<CommitOutcome> {
        let eval = self.last.take()?;
        if !eval.would_commit() {
            // Put it back — a refused evaluation is not committable; don't lose it.
            self.last = Some(eval);
            return None;
        }
        // Run the SAME draft the evaluation previewed (faithful to the preview).
        let outcome = simulate::commit(world, eval.draft());
        Some(outcome)
    }

    /// `true` iff the last evaluation predicts a commit (so [`Self::commit`] will
    /// run). `false` before any evaluation or when the last one refused.
    pub fn can_commit(&self) -> bool {
        self.last.as_ref().is_some_and(Evaluation::would_commit)
    }

    /// **DISCARD** the last evaluation — drop the what-if, leaving the world (which
    /// was never touched by a `doIt` anyway) and the composed draft as they are. The
    /// Smalltalk gesture of throwing away a scratch result. Returns `true` if there
    /// was an evaluation to discard.
    pub fn discard(&mut self) -> bool {
        self.last.take().is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reflect::{FieldValue, ObjectKind};
    use crate::simulate::EffectKind;
    use dregg_cell::CellId;

    /// A two-cell world: `a` holds 1_000, `b` holds 0 — plus the ids.
    fn two_cell_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        (w, a, b)
    }

    /// Compose a single transfer `a → b` of `amount` into a fresh workspace.
    fn transfer_workspace(a: CellId, b: CellId, amount: u64) -> Workspace {
        let mut ws = Workspace::new(a);
        let ai = ws.draft_mut().add_action(a);
        ws.draft_mut().add_effect(ai, EffectKind::Transfer { to: b, amount });
        ws
    }

    #[test]
    fn doit_evaluates_without_mutating_the_live_world() {
        let (w, a, b) = two_cell_world();
        let mut ws = transfer_workspace(a, b, 250);

        let eval = ws.evaluate(&w);
        assert!(eval.would_commit(), "a conserving transfer predicts a commit");

        // THE WHOLE POINT: a doIt is a what-if — the live world is UNTOUCHED.
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 1_000);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 0);
        assert_eq!(w.height(), 0, "no commit happened on the live world");
        assert_eq!(w.receipts().len(), 0, "no receipt appended to the live world");
    }

    #[test]
    fn printit_shows_the_predicted_receipt_for_a_good_intent() {
        let (w, a, b) = two_cell_world();
        let mut ws = transfer_workspace(a, b, 250);
        ws.evaluate(&w);

        let printed = ws.print_it().expect("evaluated");
        // The printed value is the predicted receipt summary — and it carries the
        // REAL predicted receipt hash (the SimOutcome's own receipt).
        let real_receipt = match &ws.last().unwrap().outcome {
            SimOutcome::Predicted { receipt, .. } => reflect::short_hex(&receipt.receipt_hash()),
            SimOutcome::Refused { .. } => unreachable!("good intent predicted to commit"),
        };
        assert!(printed.contains(&real_receipt), "printIt carries the real receipt: {printed}");
        assert!(printed.contains("action(s)"), "printIt names the action count: {printed}");
        assert!(printed.contains("root"), "printIt names the predicted image root: {printed}");
    }

    #[test]
    fn printit_shows_the_executor_refusal_for_a_bad_intent() {
        let (w, a, b) = two_cell_world();
        // a holds 1_000; move 9_999 — the executor must refuse in the fork.
        let mut ws = transfer_workspace(a, b, 9_999);
        let eval = ws.evaluate(&w);
        assert!(!eval.would_commit(), "an overspend predicts a refusal");

        let printed = ws.print_it().expect("evaluated");
        assert!(printed.contains("REFUSED"), "printIt shows the refusal: {printed}");
        // The refusal is the DYNAMIC executor's (in the fork), not a static rail catch.
        assert!(printed.contains("executor"), "the overspend is the executor's refusal: {printed}");

        // And the live world is untouched by the refused doIt.
        assert_eq!(w.height(), 0);
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 1_000);
    }

    #[test]
    fn inspectit_projects_the_predicted_post_state_as_live_objects() {
        let (w, a, b) = two_cell_world();
        let mut ws = transfer_workspace(a, b, 250);
        ws.evaluate(&w);

        let objs = ws.inspect_it();
        assert!(!objs.is_empty(), "a predicted commit yields inspectable post-state");

        // The image object is first — and its commitment reflects the PREDICTED
        // post-state (it differs from the live image's, because the fork advanced).
        let image = &objs[0];
        assert_eq!(image.kind, ObjectKind::Image);

        // The touched cells appear as reflective Cell objects carrying the PREDICTED
        // balances: a → 750, b → 250 (the fork's post-state, not the live world's).
        let cell_objs: Vec<&Inspectable> =
            objs.iter().filter(|o| o.kind == ObjectKind::Cell).collect();
        assert_eq!(cell_objs.len(), 2, "both touched cells are inspectable");
        let balance_of = |obj: &Inspectable| -> Option<i64> {
            obj.fields.iter().find_map(|f| match (&f.key[..], &f.value) {
                ("balance", FieldValue::Balance(v)) => Some(*v),
                _ => None,
            })
        };
        let predicted: Vec<i64> = cell_objs.iter().filter_map(|o| balance_of(o)).collect();
        assert!(predicted.contains(&750), "a's PREDICTED post-balance is inspectable: {predicted:?}");
        assert!(predicted.contains(&250), "b's PREDICTED post-balance is inspectable: {predicted:?}");

        // The live world still reads the PRE-state — inspectIt never mutated it.
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 1_000);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 0);
    }

    #[test]
    fn inspectit_is_empty_for_a_refused_evaluation() {
        let (w, a, b) = two_cell_world();
        let mut ws = transfer_workspace(a, b, 9_999); // overspend → refused
        ws.evaluate(&w);
        assert!(ws.inspect_it().is_empty(), "a refusal has no post-state to inspect");
    }

    #[test]
    fn commit_advances_the_world_and_leaves_a_receipt_matching_the_prediction() {
        // Pin the timestamp + zero costs so the predicted receipt is byte-identical
        // to the real commit's (same executor, same pre-state, same clock).
        const TS: i64 = 1_700_000_000;
        let mut w = World::with_costs_and_timestamp(dregg_turn::ComputronCosts::zero(), TS);
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);

        let mut ws = transfer_workspace(a, b, 250);
        ws.evaluate(&w);
        let predicted = match &ws.last().unwrap().outcome {
            SimOutcome::Predicted { receipt, .. } => receipt.receipt_hash(),
            SimOutcome::Refused { .. } => unreachable!(),
        };
        assert!(ws.can_commit(), "the prediction committed → commit is enabled");

        // Commit for real on the LIVE world.
        let outcome = ws.commit(&mut w).expect("a predicted-commit evaluation commits");
        let real = match outcome {
            CommitOutcome::Committed { receipt, .. } => receipt.receipt_hash(),
            CommitOutcome::Rejected { reason, .. } => panic!("real commit rejected: {reason}"),
        };
        assert_eq!(predicted, real, "the real receipt matches the predicted one");

        // The live world now reflects the committed turn.
        assert_eq!(w.height(), 1, "the world advanced one turn");
        assert_eq!(w.receipts().len(), 1, "a real receipt was appended");
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 750);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 250);

        // The evaluation was cleared by the commit (it described the pre-commit fork).
        assert!(ws.last().is_none(), "commit clears the previewed evaluation");
        assert!(!ws.can_commit());
    }

    #[test]
    fn discard_leaves_the_world_unchanged() {
        let (mut w, a, b) = two_cell_world();
        let mut ws = transfer_workspace(a, b, 250);
        ws.evaluate(&w);
        assert!(ws.last().is_some());

        assert!(ws.discard(), "there was an evaluation to discard");
        assert!(ws.last().is_none(), "the evaluation is gone");
        assert!(!ws.can_commit(), "nothing to commit after a discard");

        // The world was never touched — a discard drops a what-if that never ran live.
        assert_eq!(w.height(), 0);
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 1_000);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 0);

        // And the world is still fully usable (a real commit still works afterward).
        let t = w.turn(a, vec![crate::world::transfer(a, b, 10)]);
        assert!(w.commit_turn(t).is_committed());
        assert_eq!(w.height(), 1);
    }

    #[test]
    fn commit_refuses_when_the_prediction_refused() {
        let (mut w, a, b) = two_cell_world();
        let mut ws = transfer_workspace(a, b, 9_999); // overspend → refused
        ws.evaluate(&w);
        assert!(!ws.can_commit(), "a refused prediction is not committable");

        // commit returns None and does NOT touch the world (no gas, no advance).
        assert!(ws.commit(&mut w).is_none(), "a refused evaluation does not commit");
        assert_eq!(w.height(), 0, "the world did not advance");
        // The refused evaluation is preserved (commit put it back) so the operator
        // can read the printIt refusal rather than silently losing it.
        assert!(ws.last().is_some(), "the refused evaluation is retained, not lost");
    }

    #[test]
    fn evaluate_then_edit_then_commit_runs_the_previewed_turn_not_the_edited_one() {
        // The faithfulness guard: what you previewed is what commits. Evaluate a
        // 250-transfer, then EDIT the draft to a 999-transfer WITHOUT re-evaluating,
        // then commit — the committed turn is the 250 one the evaluation captured.
        let (mut w, a, b) = two_cell_world();
        let mut ws = transfer_workspace(a, b, 250);
        ws.evaluate(&w);

        // Mutate the live draft after the evaluation (no re-evaluate).
        let ai = ws.draft_mut().add_action(a);
        ws.draft_mut().add_effect(ai, EffectKind::Transfer { to: b, amount: 999 });

        // Commit runs the EVALUATION's captured draft (the single 250 transfer).
        let outcome = ws.commit(&mut w).expect("the captured prediction commits");
        assert!(outcome.is_committed());
        assert_eq!(
            w.ledger().get(&b).unwrap().state.balance(),
            250,
            "the committed turn is the 250 one previewed, not the edited 999 one"
        );
    }

    #[test]
    fn a_chained_evaluate_commit_loop_advances_the_world_step_by_step() {
        // The workspace IS a loop: evaluate → commit → evaluate the next → commit.
        // Each commit advances the live world; each next evaluate forks the NOW-
        // advanced world (so a chained turn threads the agent's chain head).
        let (mut w, a, b) = two_cell_world();

        for step in 0..3u64 {
            let mut ws = transfer_workspace(a, b, 100);
            ws.evaluate(&w);
            assert!(ws.can_commit(), "step {step} predicts a commit");
            let out = ws.commit(&mut w).expect("step commits");
            assert!(out.is_committed(), "step {step} commits on the live world");
            assert_eq!(w.height(), step + 1, "the world advanced to height {}", step + 1);
        }
        // Three committed 100-transfers: b holds 300, a holds 700.
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 300);
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 700);
        assert_eq!(w.receipts().len(), 3, "three real receipts on the live world");
    }

    #[test]
    fn inspectit_image_commitment_differs_from_the_live_image() {
        // inspectIt's image object is the PREDICTED post-state's commitment — it
        // must differ from the live image's root (the fork advanced; the live didn't).
        let (w, a, b) = two_cell_world();
        let live_root = w.state_root();
        let mut ws = transfer_workspace(a, b, 250);
        ws.evaluate(&w);

        let image = ws
            .inspect_it()
            .iter()
            .find(|o| o.kind == ObjectKind::Image)
            .expect("the predicted image object is present");
        let predicted_root = image.fields.iter().find_map(|f| match (&f.key[..], &f.value) {
            ("state_root", FieldValue::Hash(h)) => Some(*h),
            _ => None,
        });
        assert!(predicted_root.is_some(), "the image object carries a state_root");
        assert_ne!(
            predicted_root.unwrap(),
            live_root,
            "the predicted image commitment moved (the fork advanced; the live world did not)"
        );
    }
}
