//! **A collectively-authorable, verifiable CYOA in the tab** — the wasm realization of
//! `spween-dregg`'s single-player [`Driver`](spween_dregg::Driver), the narrative sibling
//! of [`DocCollabWorld`](crate::bindings_doc::DocCollabWorld).
//!
//! A spween story is a graph of passages; a *choice* is a cap-bounded **turn** the real
//! executor admits IFF the choice's gate passes; a *playthrough* is an **un-retconnable
//! receipt chain** a stranger can replay (`spween-dregg/src/verify.rs`). [`StoryWorld`]
//! holds a `spween-dregg` [`WorldCell`](spween_dregg::WorldCell) +
//! [`Driver`](spween_dregg::Driver) at [`NodeTarget::Local`](dregg_node_target::NodeTarget)
//! — in-process, NO networking — and exposes exactly the contract the `<dregg-story>`
//! element consumes: render the current passage, list condition-gated choices, `advance`
//! one verified turn, and `verify` the whole chain by replay.
//!
//! ## PLATFORM NOTE — this is in the shipped wasm32 bundle
//!
//! [`StoryWorld`] wraps `spween-dregg`'s real [`Driver`], whose turns are admitted by
//! `dregg-app-framework`'s [`EmbeddedExecutor`]. That executor rides the framework's
//! **wasm-clean CORE**: `spween-dregg` depends on `dregg-app-framework` with
//! `default-features = false`, dropping the `server` feature (axum/tokio-full/reqwest/
//! tower-http, non-wasm32). So this whole module — the single-player [`Driver`] surface
//! AND the collective vote surface below — compiles to wasm32 exactly the way
//! [`DocCollabWorld`](crate::bindings_doc::DocCollabWorld) does, with no target gate: it
//! is in the shipped wasm bundle and in the native `cargo test`.
//!
//! ## THE COLLECTIVE SURFACE — the crowd co-authors a verifiable CYOA in the tab
//!
//! Beyond single-player [`Self::advance`], `StoryWorld` exposes the **per-branch vote
//! flow** (the killer mode): the audience opens a poll over the current passage's
//! available choices ([`Self::open_branch_poll`]), casts one ballot each
//! ([`Self::cast_vote`]), and the winning branch fires as ONE verified turn
//! ([`Self::close_branch_poll`]) — the same one-turn advance path single-player uses. The
//! branch decision is certified by the REAL federation-grade
//! [`CollectiveChoiceEngine`](spween_dregg::CollectiveChoiceEngine) (privacy-voting
//! `WriteOnce` ballots + `Monotonic` tallies + the polis `AffineLe` quorum gate), now
//! wasm-clean — so the crowd-vote that picks a story branch is the *same engine that
//! governs a federation*. The engine gates eligibility to a declared electorate, so the
//! browser configures the eligible crowd roster once ([`Self::set_electorate`]) before
//! opening a branch poll.

use wasm_bindgen::prelude::*;

use spween_dregg::{
    CollectiveChoiceEngine, Driver, Scene, VoteEngine, VoteError, VoteOption, WorldCell, parse,
    verify,
};

/// The deterministic deploy seed. `spween-dregg` derives the world-cell identity from the
/// scene id + seed, so a fixed seed makes a playthrough re-verify against a freshly
/// re-deployed, identically-seeded world (the `verify` path's requirement).
const STORY_SEED: u8 = 7;

/// The synthetic filename a browser-supplied `.scene` source is parsed under (only feeds
/// the scene id / error spans — the source string is authoritative).
const STORY_FILENAME: &str = "story.scene";

/// **A spween story running as verifiable turns, in the tab.** Owns a `spween-dregg`
/// [`WorldCell`] + [`Driver`] at `NodeTarget::Local` (the default — in-process, no
/// networking). Each [`Self::advance`] runs the stock `spween::Runtime`'s gate-checked
/// `select_choice` and flushes the resulting cell writes as ONE cap-gated verified turn,
/// appending its receipt to the chain; [`Self::verify`] replays that chain against a fresh
/// world — the "stranger checks the story" tooth.
#[wasm_bindgen]
pub struct StoryWorld {
    /// The compiled scene. LEAKED to `'static`: a `Driver<'s>` borrows the `Scene` for its
    /// runtime, and a `#[wasm_bindgen]` struct cannot be self-referential. A `StoryWorld`
    /// lives for the page's lifetime, so one small per-story leak is the honest cost of
    /// the borrow (the alternative — an `ouroboros`/`Pin` self-reference — buys nothing
    /// here). The same `&'static Scene` re-deploys the fresh world `verify` replays.
    scene: &'static Scene,
    /// The stock-runtime driver over the world-cell; each `advance` is a verified turn.
    driver: Driver<'static>,
    /// **The eligible crowd roster** for collective (vote-driven) branching. The real
    /// [`CollectiveChoiceEngine`] gates eligibility to a declared electorate (holding a
    /// ballot cap *is* eligibility), so the tab configures who may vote once
    /// ([`Self::set_electorate`]) before opening a branch poll. Empty until configured —
    /// an unconfigured collective poll admits no ballots (fail-closed).
    electorate: Vec<String>,
    /// The currently-open branch poll, if any. Holds the live real vote engine over the
    /// current passage's available choices plus the option→spween-choice-index map.
    /// `None` between rounds (single-player `advance` still works regardless).
    poll: Option<BranchPoll>,
    /// The number of branch polls opened so far (the round counter surfaced to the crowd).
    round: usize,
}

/// One open collective branch poll: the live real vote engine plus the ballot options it
/// was opened over. Each option carries the spween `choice_index` the winner resolves to
/// (`Driver::advance`'s argument) — the option position is the ballot slot; the
/// `choice_index` is the story edge.
struct BranchPoll {
    /// The live federation-grade engine (privacy-voting ballots + monotone tallies +
    /// quorum `AffineLe`). Each [`StoryWorld::cast_vote`] is a real ballot turn on it; the
    /// winner is certified by its quorum gate at [`StoryWorld::close_branch_poll`].
    engine: CollectiveChoiceEngine,
    /// The ballot options (available choices only), in ballot order.
    options: Vec<VoteOption>,
}

#[wasm_bindgen]
impl StoryWorld {
    /// **Compile a spween `.scene` source into a verifiable world and start the
    /// playthrough.** FAIL-CLOSED: a source that does not parse to a scene is a `JsError`
    /// (no half-deployed world). The intro passage's entry effects commit as the genesis
    /// turn, so the story's first receipt exists before any choice is taken.
    #[wasm_bindgen(constructor)]
    pub fn new(scene_source: String) -> Result<StoryWorld, JsError> {
        Self::try_new(&scene_source).map_err(|e| JsError::new(&e))
    }

    /// The fallible core — `String` errors, wasm-bindgen-free, so the fail-closed path is
    /// testable NATIVELY (constructing a `JsError` panics off-wasm). `new` wraps this in
    /// `JsError`. Fail-closed: an unparseable scene / failed deploy mints no world.
    fn try_new(scene_source: &str) -> Result<StoryWorld, String> {
        let scene = parse(scene_source, STORY_FILENAME).map_err(|e| e.to_string())?;
        // Leak the scene to `'static` so the borrowing `Driver` can be owned by this struct.
        let scene: &'static Scene = Box::leak(Box::new(scene));

        let world = WorldCell::deploy(scene, STORY_SEED).map_err(|e| e.to_string())?;
        let driver = Driver::start(world, scene).map_err(|e| e.to_string())?;

        Ok(StoryWorld {
            scene,
            driver,
            electorate: Vec::new(),
            poll: None,
            round: 0,
        })
    }

    /// The current passage name (empty once the scene has ended).
    #[wasm_bindgen(js_name = currentPassage)]
    pub fn current_passage(&self) -> String {
        self.driver.current_passage().unwrap_or_default()
    }

    /// The current passage's narrative prose — the text to render. Reads spween's own
    /// per-passage prose (`Runtime::current_prose`); empty once the scene has ended.
    #[wasm_bindgen(js_name = passageProse)]
    pub fn passage_prose(&self) -> String {
        self.driver.prose().unwrap_or_default()
    }

    /// The choices at the current passage as JSON: `[{index, text, available}]`.
    /// `available` is the condition-gated availability the stock runtime already computes
    /// against the cell-backed state (`spween-dregg`'s [`ChoiceView`](spween_dregg::ChoiceView)).
    /// The `<dregg-story>` element renders an unavailable choice as disabled; a call to
    /// [`Self::advance`] on it is refused in-band regardless (fail-closed at the turn).
    #[wasm_bindgen(js_name = choicesJson)]
    pub fn choices_json(&self) -> String {
        use serde_json::json;
        let rows: Vec<serde_json::Value> = self
            .driver
            .choices()
            .into_iter()
            .map(|c| {
                json!({
                    "index": c.index,
                    "text": c.text,
                    "available": c.available,
                })
            })
            .collect();
        json!(rows).to_string()
    }

    /// **Advance the story by taking choice `index` — as ONE verified turn.** Runs the
    /// stock `select_choice` (which checks the gate, runs the effects, navigates) and
    /// flushes the buffered cell writes as a single cap-gated turn, appending its receipt.
    ///
    /// Returns JSON `{ ok, passage, receiptCount, commitmentHex, error? }`. FAIL-CLOSED: a
    /// gated (condition-not-met) or out-of-range choice — or a choice on an already-ended
    /// scene — returns `{ ok: false, error }` and NOTHING commits (`receiptCount` and
    /// `commitmentHex` still describe the last good state). This is the story advancing
    /// only ever along an eligible edge.
    pub fn advance(&mut self, index: usize) -> String {
        use serde_json::json;
        match self.driver.advance(index) {
            Ok(_step) => json!({
                "ok": true,
                "passage": self.current_passage(),
                "receiptCount": self.receipt_count(),
                "commitmentHex": self.commitment_hex(),
            })
            .to_string(),
            Err(e) => json!({
                "ok": false,
                "passage": self.current_passage(),
                "receiptCount": self.receipt_count(),
                "commitmentHex": self.commitment_hex(),
                "error": e.to_string(),
            })
            .to_string(),
        }
    }

    /// **Verify the whole playthrough by replay** — the un-retconnable "stranger checks the
    /// story" check. Re-drives a FRESH, identically-seeded world through the recorded choice
    /// sequence and confirms it reproduces the exact committed state at every step, AND that
    /// the receipt chain links cleanly (`spween-dregg/src/verify.rs` — both teeth). A forged
    /// (ineligible) choice is refused by the executor on replay; a tampered receipt breaks
    /// the chain. Returns `true` iff the playthrough is authentic.
    pub fn verify(&self) -> bool {
        let Ok(fresh) = WorldCell::deploy(self.scene, STORY_SEED) else {
            return false;
        };
        verify(fresh, self.scene, &self.driver.playthrough()).is_ok()
    }

    /// The world-cell's current committed state commitment (hex) — the `post_state_hash` of
    /// the last committed turn (genesis if no choice has been taken yet). This is the
    /// stranger's check surface: it MOVES on every advance and pins exactly one committed
    /// history.
    #[wasm_bindgen(js_name = commitmentHex)]
    pub fn commitment_hex(&self) -> String {
        let last = self
            .driver
            .steps()
            .last()
            .map(|s| &s.receipt)
            .or_else(|| self.driver.genesis());
        match last {
            Some(r) => crate::bindings::hex_encode(&r.post_state_hash),
            None => String::new(),
        }
    }

    /// The committed-receipt count — the audit-tape length (the genesis turn plus one per
    /// advanced choice). Proves each advance was a real verified turn, not a local poke.
    #[wasm_bindgen(js_name = receiptCount)]
    pub fn receipt_count(&self) -> usize {
        // genesis (1, once started) + one per committed choice-step.
        let genesis = usize::from(self.driver.genesis().is_some());
        genesis + self.driver.steps().len()
    }

    /// Whether the scene has ended (no further choices).
    #[wasm_bindgen(js_name = isEnded)]
    pub fn is_ended(&self) -> bool {
        self.driver.is_ended()
    }
}

/// The quorum threshold for a branch poll: `1`, so the crowd resolves by **plurality** —
/// any single ballot lets the poll resolve, and the winner is the argmax of the tally
/// (the [`CollectiveChoiceEngine`]'s `AffineLe` gate certifies once `Σ TALLY ≥ 1`). A
/// poll with ZERO ballots is below quorum and does not resolve (fail-closed: nothing
/// advances).
const BRANCH_QUORUM_M: u64 = 1;

// ── THE COLLECTIVE SURFACE — the crowd co-authors the story, per branch ────────────────
//
// A second `#[wasm_bindgen] impl` block (the single-player surface above is untouched):
// open a poll over the current passage's available choices, the audience casts one ballot
// each on the REAL federation-grade `CollectiveChoiceEngine`, and the winning branch fires
// as ONE verified turn — the same `Driver::advance` path single-player uses.
#[wasm_bindgen]
impl StoryWorld {
    /// **Configure the eligible crowd roster** for collective branching — a
    /// comma-separated list of voter ids (whitespace trimmed, empties dropped). The real
    /// [`CollectiveChoiceEngine`] gates eligibility to this declared electorate: only a
    /// listed voter can hold a ballot cap, so a poll opened after this admits exactly
    /// these voters' ballots. Re-calling replaces the roster (it takes effect on the NEXT
    /// [`Self::open_branch_poll`]; the current poll keeps the electorate it opened with).
    #[wasm_bindgen(js_name = setElectorate)]
    pub fn set_electorate(&mut self, voters_csv: String) {
        self.electorate = voters_csv
            .split(',')
            .map(str::trim)
            .filter(|v| !v.is_empty())
            .map(str::to_string)
            .collect();
    }

    /// The configured electorate as JSON `[voterId]` (the eligible crowd roster).
    #[wasm_bindgen(js_name = electorateJson)]
    pub fn electorate_json(&self) -> String {
        serde_json::json!(self.electorate).to_string()
    }

    /// **OPEN A BRANCH POLL over the current passage's AVAILABLE choices.** Returns JSON
    /// `{ passage, round, options: [{ choiceIndex, label }] }`. FAIL-CLOSED: if the scene
    /// has ended or the current passage offers no available choice, returns `{ error }`
    /// and opens nothing (the crowd cannot vote on a branch that does not exist). Only
    /// AVAILABLE choices (the runtime's gate already enforced) go on the ballot, mapped to
    /// [`VoteOption`]s; the option→`choice_index` map is held for the close. Opening
    /// REPLACES any prior open poll (a fresh round).
    #[wasm_bindgen(js_name = openBranchPoll)]
    pub fn open_branch_poll(&mut self) -> String {
        use serde_json::json;

        if self.driver.is_ended() {
            return json!({ "error": "the scene has ended — no branch to vote on" }).to_string();
        }
        let Some(passage) = self.driver.current_passage() else {
            return json!({ "error": "no current passage to poll" }).to_string();
        };
        // Only AVAILABLE choices go on the ballot (the runtime's gate is authoritative);
        // an unavailable/gated choice is never a votable option (fail-closed at the ballot).
        let options: Vec<VoteOption> = self
            .driver
            .choices()
            .into_iter()
            .filter(|c| c.available)
            .map(|c| VoteOption {
                choice_index: c.index,
                label: c.text.clone(),
            })
            .collect();
        if options.is_empty() {
            return json!({ "error": "no available choices at this passage to poll" }).to_string();
        }

        // Construct the REAL engine over the configured electorate and open the poll (a
        // real `OPEN` turn on the collective_choice substrate).
        let roster: Vec<&str> = self.electorate.iter().map(String::as_str).collect();
        let mut engine = CollectiveChoiceEngine::new(&roster, BRANCH_QUORUM_M);
        if let Err(e) = engine.open_poll(&options) {
            return json!({ "error": format!("open poll refused: {e}") }).to_string();
        }

        self.round += 1;
        let round = self.round;
        let rows: Vec<serde_json::Value> = options
            .iter()
            .map(|o| json!({ "choiceIndex": o.choice_index, "label": o.label }))
            .collect();
        self.poll = Some(BranchPoll { engine, options });
        json!({ "passage": passage, "round": round, "options": rows }).to_string()
    }

    /// **CAST ONE BALLOT** — `voter` picks ballot option `option_index` (a real
    /// `cast_vote` turn on the collective_choice engine). Returns JSON
    /// `{ ok, tally: [{ label, count }], error? }`. ONE vote per voter: a second ballot
    /// from the same voter hits the ballot's consumed nullifier and is refused
    /// (`{ ok: false, error }`), the tally unchanged. FAIL-CLOSED: no open poll, an
    /// out-of-range option, or a voter outside the configured electorate all return
    /// `{ ok: false, error }` and nothing counts.
    #[wasm_bindgen(js_name = castVote)]
    pub fn cast_vote(&mut self, voter: String, option_index: usize) -> String {
        use serde_json::json;

        let Some(poll) = self.poll.as_mut() else {
            return json!({ "ok": false, "tally": [], "error": "no branch poll is open" })
                .to_string();
        };
        match poll.engine.cast(&voter, option_index) {
            Ok(()) => json!({
                "ok": true,
                "tally": tally_rows(&poll.options, &poll.engine.tally()),
            })
            .to_string(),
            Err(e) => json!({
                "ok": false,
                "tally": tally_rows(&poll.options, &poll.engine.tally()),
                "error": vote_error_message(&e),
            })
            .to_string(),
        }
    }

    /// The current branch tally as JSON `[{ label, count }]` (in ballot-option order).
    /// Empty when no poll is open.
    #[wasm_bindgen(js_name = branchTally)]
    pub fn branch_tally(&self) -> String {
        match self.poll.as_ref() {
            Some(poll) => {
                serde_json::json!(tally_rows(&poll.options, &poll.engine.tally())).to_string()
            }
            None => "[]".to_string(),
        }
    }

    /// **CLOSE THE POLL and ADVANCE the story along the winning branch — as ONE verified
    /// turn.** Resolves the winner off the (monotone) tally through the engine's quorum
    /// `AffineLe` gate, maps the winning ballot option to its spween `choice_index`, and
    /// fires it via [`Driver::advance`] — the exact one-cap-gated-turn path single-player
    /// uses. Returns JSON `{ ok, winningChoice, winningLabel, tally, passage,
    /// receiptCount, commitmentHex, error? }` — `winningChoice` is the spween choice index,
    /// `passage` the new passage, and `receiptCount`/`commitmentHex` the grown audit tape.
    ///
    /// FAIL-CLOSED: with no open poll, or no ballots cast (below quorum), the poll does not
    /// resolve — returns `{ ok: false, error }`, NOTHING advances, and (for the no-ballots
    /// case) the poll stays OPEN so the crowd can keep voting. A resolved winner that the
    /// executor then refuses also returns `{ ok: false, error }` with nothing committed.
    #[wasm_bindgen(js_name = closeBranchPoll)]
    pub fn close_branch_poll(&mut self) -> String {
        use serde_json::json;

        let Some(poll) = self.poll.as_mut() else {
            return json!({ "ok": false, "error": "no branch poll is open" }).to_string();
        };

        // Resolve the winner through the real quorum gate. Below quorum (no ballots) the
        // gate refuses the RESOLVED turn — nothing advances, the poll stays open.
        let tally_now = tally_rows(&poll.options, &poll.engine.tally());
        let winning_option = match poll.engine.resolve() {
            Ok(opt) => opt,
            Err(e) => {
                return json!({
                    "ok": false,
                    "tally": tally_now,
                    "error": vote_error_message(&e),
                })
                .to_string();
            }
        };
        let winning_choice = poll.options[winning_option].choice_index;
        let winning_label = poll.options[winning_option].label.clone();

        // Fire the winning branch as ONE verified turn (the same path single-player uses).
        let advance = self.driver.advance(winning_choice);
        // The round resolved: consume the poll regardless (a resolved poll is terminal).
        self.poll = None;
        match advance {
            Ok(_step) => json!({
                "ok": true,
                "winningChoice": winning_choice,
                "winningLabel": winning_label,
                "tally": tally_now,
                "passage": self.current_passage(),
                "receiptCount": self.receipt_count(),
                "commitmentHex": self.commitment_hex(),
            })
            .to_string(),
            Err(e) => json!({
                "ok": false,
                "winningChoice": winning_choice,
                "winningLabel": winning_label,
                "tally": tally_now,
                "passage": self.current_passage(),
                "receiptCount": self.receipt_count(),
                "commitmentHex": self.commitment_hex(),
                "error": e.to_string(),
            })
            .to_string(),
        }
    }

    /// Whether a collective branch poll is currently open.
    #[wasm_bindgen(js_name = hasOpenPoll)]
    pub fn has_open_poll(&self) -> bool {
        self.poll.is_some()
    }
}

/// A tally as `[{ label, count }]` rows (ballot-option order) — the JSON both `castVote`
/// and `branchTally` surface. `tally` is one count per option (as `VoteEngine::tally`
/// returns); a short/absent tally reads as zero counts.
fn tally_rows(options: &[VoteOption], tally: &[u64]) -> serde_json::Value {
    use serde_json::json;
    let rows: Vec<serde_json::Value> = options
        .iter()
        .enumerate()
        .map(|(i, o)| json!({ "label": o.label, "count": tally.get(i).copied().unwrap_or(0) }))
        .collect();
    json!(rows)
}

/// A human-readable reason for a [`VoteError`] — the `error` string the collective surface
/// returns (double-vote, bad option, ineligible voter, no poll, below-quorum, …).
fn vote_error_message(e: &VoteError) -> String {
    e.to_string()
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    /// A 3-passage tavern story with a numeric gate (`perception >= 10`, unset ⇒ refused),
    /// plain-choice navigation, and an end. The `<dregg-story>` contract exercised here is
    /// exactly what the browser element calls.
    const TAVERN: &str = r#"---
id: tavern_encounter
title: The Mysterious Stranger
weight: 10
---

=== intro

A hooded figure sits alone in the corner of the tavern.
They gesture for you to approach.

* [Approach cautiously] { perception >= 10 }
  ~ perception_used = true
  -> cautious

* [Approach boldly]
  -> bold

=== bold

You stride over confidently. The stranger seems amused
by your directness.

* [Sit down]
  ~ stranger_trust += 1
  -> conversation

=== cautious

You notice a glint of steel beneath their cloak.

* [Sit down]
  ~ stranger_trust += 2
  -> conversation

=== conversation

The stranger leans close and whispers of an artifact.

* [Thank them and leave]
  -> END
"#;

    /// THE STORY LOOP: compile a real `.scene`, advance through choices as verified turns
    /// (the passage changes + the receipt count grows), a GATED choice is refused
    /// (fail-closed, nothing commits), and the honest playthrough replays true.
    #[test]
    fn story_advances_as_verified_turns_and_reverifies() {
        let mut story = StoryWorld::new(TAVERN.to_string()).expect("the tavern scene compiles");

        // Genesis is committed before any choice: one receipt, we are at `intro`.
        assert_eq!(story.current_passage(), "intro");
        assert_eq!(story.receipt_count(), 1, "the genesis turn is committed");
        assert!(!story.passage_prose().is_empty(), "the intro renders prose");
        assert!(!story.commitment_hex().is_empty());

        // The choices: index 0 "Approach cautiously" is GATED (perception unset ⇒ < 10 ⇒
        // unavailable); index 1 "Approach boldly" is open.
        let choices: serde_json::Value =
            serde_json::from_str(&story.choices_json()).expect("choices are JSON");
        let choices = choices.as_array().expect("a choice array");
        assert_eq!(choices.len(), 2);
        assert_eq!(choices[0]["available"], serde_json::json!(false));
        assert_eq!(choices[1]["available"], serde_json::json!(true));

        // FAIL-CLOSED: advancing the GATED choice is refused; NOTHING commits.
        let refused: serde_json::Value =
            serde_json::from_str(&story.advance(0)).expect("advance returns JSON");
        assert_eq!(
            refused["ok"],
            serde_json::json!(false),
            "gated choice refused"
        );
        assert!(refused.get("error").is_some(), "the refusal carries a why");
        assert_eq!(
            story.current_passage(),
            "intro",
            "still at intro; nothing moved"
        );
        assert_eq!(
            story.receipt_count(),
            1,
            "no turn committed on a refused choice"
        );

        // Advance the OPEN choice (index 1): a real verified turn → `bold`, receipts grow.
        let ok: serde_json::Value =
            serde_json::from_str(&story.advance(1)).expect("advance returns JSON");
        assert_eq!(ok["ok"], serde_json::json!(true));
        assert_eq!(ok["passage"], serde_json::json!("bold"));
        assert_eq!(story.current_passage(), "bold");
        assert_eq!(story.receipt_count(), 2, "one advance = one new receipt");

        // Advance again: bold → conversation (its only choice, index 0).
        let ok2: serde_json::Value =
            serde_json::from_str(&story.advance(0)).expect("advance returns JSON");
        assert_eq!(ok2["ok"], serde_json::json!(true));
        assert_eq!(story.current_passage(), "conversation");
        assert_eq!(story.receipt_count(), 3);

        // And into the ending.
        let done: serde_json::Value =
            serde_json::from_str(&story.advance(0)).expect("advance returns JSON");
        assert_eq!(done["ok"], serde_json::json!(true));
        assert!(story.is_ended(), "the scene ended");
        assert_eq!(story.receipt_count(), 4, "genesis + 3 committed choices");

        // THE STRANGER CHECK: the honest playthrough replays true.
        assert!(story.verify(), "the honest playthrough re-verifies");
    }

    /// A bad scene FAILS CLOSED — no `StoryWorld` is minted from unparseable source.
    #[test]
    fn bad_scene_is_fail_closed() {
        let broken = StoryWorld::try_new("this is not a spween scene {{{");
        assert!(broken.is_err(), "an unparseable scene mints no world");
    }

    /// TAMPER a receipt in the recorded playthrough → `verify` (both teeth) rejects it.
    /// The `StoryWorld` API itself never exposes a mutate-the-tape door; this reaches into
    /// `spween-dregg`'s public `Playthrough` to corrupt a `post_state_hash`, breaking the
    /// hash-chain linkage the un-retconnable check rests on.
    #[test]
    fn tampered_receipt_fails_verification() {
        use spween_dregg::Playthrough;
        let mut story = StoryWorld::new(TAVERN.to_string()).expect("compile");
        let _ = story.advance(1); // intro -> bold
        let _ = story.advance(0); // bold  -> conversation

        // The honest chain verifies.
        assert!(story.verify(), "honest chain verifies before tamper");

        // Corrupt the genesis receipt's post_state_hash → the next receipt's pre_state_hash
        // no longer links (LinkageBroken / a diverged replay state).
        let mut tampered: Playthrough = story.driver.playthrough();
        tampered.genesis.post_state_hash = [0xAB; 32];
        let fresh = WorldCell::deploy(story.scene, STORY_SEED).expect("fresh world");
        assert!(
            verify(fresh, story.scene, &tampered).is_err(),
            "a tampered receipt chain is refused"
        );
    }

    /// A 3-passage story with a real branch at `intro`: TWO available (ungated) choices,
    /// each leading to an ending. The collective surface polls that branch.
    const CROSSROADS: &str = r#"---
id: crossroads
title: The Crossroads
weight: 10
---

=== intro

You reach a fork in the road at dusk.

* [Take the left path]
  -> left

* [Take the right path]
  -> right

=== left

A quiet meadow opens before you. The road ends here.

* [Rest]
  -> END

=== right

A dark forest looms ahead.

* [Rest]
  -> END
"#;

    /// THE COLLECTIVE LOOP (the killer mode): the crowd co-authors the branch. Configure
    /// the electorate → open a branch poll (2 options) → cast three ballots (2 for option
    /// 0, 1 for option 1; a double-vote by the same voter is REFUSED) → the tally shows
    /// [2, 1] → close the poll: the winning branch fires as ONE verified turn (the story
    /// advances, the receipt tape grows), and the whole playthrough replays true. Then the
    /// two fail-closed teeth: closing with no votes / no open poll advances NOTHING.
    #[test]
    fn collective_vote_drives_a_branch_as_one_verified_turn() {
        let mut story = StoryWorld::new(CROSSROADS.to_string()).expect("crossroads compiles");

        // Genesis committed; we are at the branching passage with two open choices.
        assert_eq!(story.current_passage(), "intro");
        assert_eq!(story.receipt_count(), 1, "genesis turn committed");

        // FAIL-CLOSED: closing before anything is open advances nothing.
        let no_poll: serde_json::Value =
            serde_json::from_str(&story.close_branch_poll()).expect("JSON");
        assert_eq!(no_poll["ok"], serde_json::json!(false), "no open poll");
        assert_eq!(story.receipt_count(), 1, "nothing advanced");

        // The eligible crowd (the real engine gates eligibility to this roster).
        story.set_electorate("alice, bob, carol".to_string());

        // OPEN the branch poll: two available choices → two ballot options.
        let opened: serde_json::Value =
            serde_json::from_str(&story.open_branch_poll()).expect("JSON");
        assert!(opened.get("error").is_none(), "poll opened");
        assert_eq!(opened["passage"], serde_json::json!("intro"));
        assert_eq!(opened["round"], serde_json::json!(1));
        let options = opened["options"].as_array().expect("options array");
        assert_eq!(options.len(), 2, "two available choices → two options");
        assert!(story.has_open_poll());
        // The spween choice index each ballot option resolves to.
        let opt0_choice = options[0]["choiceIndex"].as_u64().unwrap() as usize;

        // CAST three ballots: alice+bob → option 0, carol → option 1.
        for (voter, opt) in [("alice", 0usize), ("bob", 0), ("carol", 1)] {
            let cast: serde_json::Value =
                serde_json::from_str(&story.cast_vote(voter.to_string(), opt)).expect("JSON");
            assert_eq!(cast["ok"], serde_json::json!(true), "{voter} voted");
        }

        // ONE VOTE PER VOTER: alice's second ballot is REFUSED, the tally unchanged.
        let dbl: serde_json::Value =
            serde_json::from_str(&story.cast_vote("alice".to_string(), 1)).expect("JSON");
        assert_eq!(dbl["ok"], serde_json::json!(false), "double-vote refused");
        assert!(dbl.get("error").is_some(), "the refusal carries a why");

        // A voter OUTSIDE the electorate is refused (real eligibility gate).
        let stranger: serde_json::Value =
            serde_json::from_str(&story.cast_vote("mallory".to_string(), 0)).expect("JSON");
        assert_eq!(
            stranger["ok"],
            serde_json::json!(false),
            "ineligible voter refused"
        );

        // The tally is [2, 1].
        let tally: serde_json::Value = serde_json::from_str(&story.branch_tally()).expect("JSON");
        let tally = tally.as_array().expect("tally array");
        assert_eq!(
            tally[0]["count"],
            serde_json::json!(2),
            "option 0 = 2 votes"
        );
        assert_eq!(tally[1]["count"], serde_json::json!(1), "option 1 = 1 vote");

        // CLOSE: option 0 (argmax) wins; the branch fires as one verified turn.
        let closed: serde_json::Value =
            serde_json::from_str(&story.close_branch_poll()).expect("JSON");
        assert_eq!(closed["ok"], serde_json::json!(true), "the branch resolved");
        assert_eq!(
            closed["winningChoice"].as_u64().unwrap() as usize,
            opt0_choice,
            "the winner is option 0's spween choice_index"
        );
        assert_eq!(
            closed["passage"],
            serde_json::json!("left"),
            "advanced to left"
        );
        assert_eq!(story.current_passage(), "left");
        assert_eq!(
            closed["receiptCount"],
            serde_json::json!(2),
            "one advance = one receipt"
        );
        assert_eq!(
            story.receipt_count(),
            2,
            "the winning branch committed a real turn"
        );
        assert!(!story.has_open_poll(), "the poll is consumed on close");

        // THE STRANGER CHECK: the collectively-authored playthrough replays true.
        assert!(
            story.verify(),
            "the collectively-driven playthrough re-verifies"
        );

        // FAIL-CLOSED (no votes): open a fresh poll at `left`, close with zero ballots →
        // below quorum, nothing advances, the poll stays open.
        let opened2: serde_json::Value =
            serde_json::from_str(&story.open_branch_poll()).expect("JSON");
        assert!(
            opened2.get("error").is_none(),
            "second poll opened at `left`"
        );
        let empty_close: serde_json::Value =
            serde_json::from_str(&story.close_branch_poll()).expect("JSON");
        assert_eq!(
            empty_close["ok"],
            serde_json::json!(false),
            "no votes → no resolve"
        );
        assert_eq!(
            story.current_passage(),
            "left",
            "still at left; nothing advanced"
        );
        assert_eq!(
            story.receipt_count(),
            2,
            "no turn committed on an empty poll"
        );
        assert!(
            story.has_open_poll(),
            "an unresolved (no-vote) poll stays open"
        );
    }

    /// FAIL-CLOSED at an ENDED scene: no branch poll can open once the story is over.
    #[test]
    fn no_branch_poll_on_an_ended_scene() {
        let mut story = StoryWorld::new(CROSSROADS.to_string()).expect("compile");
        story.set_electorate("alice,bob,carol".to_string());

        // Drive to the end single-player: intro -> left -> END.
        assert_eq!(story.driver.advance(0).map(|_| ()).is_ok(), true);
        assert_eq!(story.current_passage(), "left");
        let _ = story.driver.advance(0); // left -> END
        assert!(story.is_ended(), "the scene ended");

        let ended: serde_json::Value =
            serde_json::from_str(&story.open_branch_poll()).expect("JSON");
        assert!(
            ended.get("error").is_some(),
            "no poll opens on an ended scene"
        );
        assert!(!story.has_open_poll(), "nothing opened");
    }
}
