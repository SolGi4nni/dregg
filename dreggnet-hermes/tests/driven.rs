//! **The driven end-to-end proof** — OFFERING #1, DRIVEN over the REAL confined +
//! metered agent substrate (`dregg_sdk::ToolGateway` rate caps + `Charge` budget),
//! with a mock/scripted brain (no LLM):
//!
//! - open a [`HermesOffering`] session — a confined agent (a jailed per-session
//!   runtime + root token);
//! - a mock-brain in-mandate prompt drives ONE confined, metered turn → a real
//!   [`TurnReceipt`] ([`Outcome::Landed`]);
//! - a rate-exhausted prompt is a real executor refusal ([`Outcome::Refused`]) that
//!   commits nothing — the confinement bites — and it is NON-VACUOUS: the SAME
//!   prompt committed a turn when the cap allowed;
//! - an over-VALUE-budget prompt is a real refusal on the distinct `Charge` leg;
//! - [`Offering::verify`] re-verifies the whole confinement chain by replay;
//! - [`Offering::render`] produces a deos affordance [`Surface`] (a `ViewNode`).

use dreggnet_hermes::{Confinement, HermesOffering, TURN_PROMPT, ToolKind};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, RunCost, SessionConfig};

/// A `prompt` affordance carrying the user's input text in the label.
fn prompt(text: &str) -> Action {
    Action::new(text, TURN_PROMPT, 0, true)
}

fn user() -> DreggIdentity {
    DreggIdentity("user:alice".to_string())
}

/// Open a confined session, list its cap-gated tool-class affordances, and confirm
/// the price is the free tier by default (the paid tier prices the confined brain).
#[test]
fn open_lists_cap_gated_tool_classes_and_prices() {
    let off = HermesOffering::new();
    let s = off
        .open(SessionConfig::with_seed(3))
        .expect("the agent opens");

    let acts = off.actions(&s);
    assert_eq!(
        acts.len(),
        ToolKind::ALL.len(),
        "one affordance per tool class"
    );
    assert!(
        acts.iter().all(|a| a.turn == TURN_PROMPT && a.enabled),
        "a fresh session's classes all have head-room (enabled)"
    );

    assert_eq!(
        off.price(&prompt("hi")),
        RunCost::free(),
        "default is the free tier"
    );
    assert_eq!(
        HermesOffering::new()
            .with_inference_credits(2)
            .price(&prompt("hi")),
        RunCost::credits(2),
        "the paid tier prices the confined inference"
    );
}

/// Drive a mock-brain in-mandate prompt — ONE confined, metered turn — and confirm a
/// REAL committed `TurnReceipt` (a genuine, nonzero 64-hex turn hash), the rate meter
/// advances, the value budget is debited, and the chain re-verifies by replay.
#[test]
fn a_mock_brain_in_mandate_prompt_drives_one_metered_receipted_turn() {
    let off = HermesOffering::scripted();
    let mut s = off.open(SessionConfig::with_seed(11)).expect("open");
    assert_eq!(s.committed_turns(), 0, "no turns committed yet");

    let rate_before = s.rate_remaining(ToolKind::Read);
    let budget_before = s.budget_remaining(ToolKind::Read);

    match off.advance(&mut s, prompt("read README.md"), user()) {
        Outcome::Landed { receipt, ended } => {
            assert!(!ended, "a confined turn does not end the session");
            assert_ne!(
                receipt.turn_hash, [0u8; 32],
                "a genuine committed turn hash"
            );
        }
        other => panic!("an in-mandate prompt must land a real receipt, got {other:?}"),
    }

    assert_eq!(s.committed_turns(), 1, "one real metered turn committed");
    assert_eq!(
        s.rate_remaining(ToolKind::Read),
        rate_before - 1,
        "the Read rate meter advanced by one"
    );
    assert_eq!(
        s.budget_remaining(ToolKind::Read),
        budget_before - 1,
        "the Read value budget was debited by the per-call charge"
    );
    // The committed step carries a genuine 64-hex receipt.
    let step = &s.steps()[0];
    assert_eq!(step.kind, ToolKind::Read);
    let receipt = step.receipt.clone().expect("a landed step has a receipt");
    assert_eq!(receipt.len(), 64, "a hex-encoded 32-byte turn hash");
    assert!(receipt.chars().all(|c| c.is_ascii_hexdigit()));

    let report = off.verify(&s);
    assert!(
        report.verified,
        "the confined chain re-verifies: {}",
        report.detail
    );
    assert_eq!(report.turns, 1);
}

/// **The confinement tooth (RATE), non-vacuous.** Execute confined to rate 1: the
/// mock brain proposes a `run` twice; the FIRST commits a real turn, the SECOND —
/// the SAME action shape — is a real executor refusal that commits nothing and does
/// not advance the meter. The agent CANNOT exceed its cell's mandate no matter what
/// its brain proposes. The honest prefix still re-verifies.
#[test]
fn a_rate_exhausted_prompt_is_refused_no_turn_non_vacuous() {
    let off = HermesOffering::scripted()
        .with_confinement(Confinement::default().with_rate(ToolKind::Execute, 1));
    let mut s = off.open(SessionConfig::with_seed(5)).expect("open");

    // The SAME action shape commits when the cap allows (non-vacuity, half 1).
    match off.advance(&mut s, prompt("run ls -la"), user()) {
        Outcome::Landed { receipt, .. } => {
            assert_ne!(
                receipt.turn_hash, [0u8; 32],
                "the first run commits a real turn"
            )
        }
        other => panic!("the first Execute call must land, got {other:?}"),
    }
    assert_eq!(s.committed_turns(), 1);

    // ...and is REFUSED when the rate mandate is exhausted (non-vacuity, half 2).
    match off.advance(&mut s, prompt("run whoami"), user()) {
        Outcome::Refused(reason) => {
            assert!(
                reason.contains("rate exhausted"),
                "the refusal names the rate leg: {reason}"
            );
        }
        other => panic!("the second Execute call must be refused, got {other:?}"),
    }
    assert_eq!(s.committed_turns(), 1, "the refused turn committed nothing");
    assert_eq!(
        s.rate_remaining(ToolKind::Execute),
        0,
        "the refusal did not push the meter past the ceiling"
    );

    assert!(
        off.verify(&s).verified,
        "the honest prefix re-verifies after the confinement refusal"
    );
}

/// **The confinement tooth (VALUE BUDGET), a distinct leg.** Fetch given a value
/// budget of 1 (below its rate): the first fetch commits (spends the 1-unit budget),
/// the second is refused on the `Charge`/OverBudget leg — distinct from the rate leg,
/// which still has head-room. Proves BOTH mandate teeth are real substrate.
#[test]
fn an_over_value_budget_prompt_is_refused_on_the_charge_leg() {
    // Fetch: generous rate (50), but a value budget of exactly 1 call.
    let off = HermesOffering::scripted()
        .with_confinement(Confinement::default().with_budget(ToolKind::Fetch, 1));
    let mut s = off.open(SessionConfig::with_seed(6)).expect("open");

    assert!(
        off.advance(&mut s, prompt("fetch https://dregg.net"), user())
            .landed(),
        "the first fetch commits within budget"
    );
    assert!(
        s.rate_remaining(ToolKind::Fetch) > 0,
        "the RATE still has head-room — only the value budget is spent"
    );
    assert_eq!(
        s.budget_remaining(ToolKind::Fetch),
        0,
        "the value budget is spent"
    );

    match off.advance(&mut s, prompt("fetch https://example.com"), user()) {
        Outcome::Refused(reason) => assert!(
            reason.contains("value budget exhausted"),
            "the refusal names the VALUE-budget leg (distinct from rate): {reason}"
        ),
        other => panic!("the over-budget fetch must be refused, got {other:?}"),
    }
    assert_eq!(
        s.committed_turns(),
        1,
        "the over-budget turn committed nothing"
    );
    assert!(off.verify(&s).verified, "the honest prefix re-verifies");
}

/// A denied class (rate 0) fails closed on the FIRST attempt — the confinement can
/// deny a whole tool class, and a live-brain proposal for it never commits.
#[test]
fn a_denied_class_fails_closed_on_first_attempt() {
    let off = HermesOffering::scripted()
        .with_confinement(Confinement::default().with_rate(ToolKind::Edit, 0));
    let mut s = off.open(SessionConfig::with_seed(2)).expect("open");

    match off.advance(&mut s, prompt("write secrets.txt leak"), user()) {
        Outcome::Refused(reason) => assert!(reason.contains("rate exhausted"), "{reason}"),
        other => panic!("a denied class must refuse on first attempt, got {other:?}"),
    }
    assert_eq!(
        s.committed_turns(),
        0,
        "nothing committed for a denied class"
    );
    // The affordance for a denied class renders as a dimmed (!enabled) row.
    let edit = off
        .actions(&s)
        .into_iter()
        .find(|a| a.arg == ToolKind::Edit.tool_id())
        .expect("the Edit affordance is offered");
    assert!(
        !edit.enabled,
        "a denied class is a dimmed cap-tooth affordance"
    );
}

/// A mixed session: multiple classes driven, each independently metered; `render`
/// produces a deos affordance `Surface` naming the agent + a cap-gated class menu;
/// the whole confinement chain re-verifies by replay.
#[test]
fn a_mixed_session_renders_a_surface_and_re_verifies() {
    let off = HermesOffering::scripted();
    let mut s = off.open(SessionConfig::with_seed(42)).expect("open");
    let actor = user();

    for input in [
        "read a.txt",
        "search foo",
        "read b.txt",
        "hello agent",
        "run ls",
    ] {
        assert!(
            off.advance(&mut s, prompt(input), actor.clone()).landed(),
            "in-mandate `{input}` lands"
        );
    }
    // Classes are independently metered.
    assert_eq!(
        s.rate_remaining(ToolKind::Read),
        ToolKind::Read.default_rate() - 2,
        "two Read turns metered"
    );
    assert_eq!(
        s.rate_remaining(ToolKind::Search),
        ToolKind::Search.default_rate() - 1,
        "one Search turn metered"
    );
    assert_eq!(s.committed_turns(), 5, "five real metered turns committed");

    // render → a deos ViewNode Section titled with the agent name.
    let surface = off.render(&s);
    match surface.view() {
        deos_view::ViewNode::Section {
            title, children, ..
        } => {
            assert!(
                title.starts_with("Hosted Hermes"),
                "the surface names the agent"
            );
            // The class menu is present.
            let has_menu = children.iter().any(|c| {
                matches!(
                    c,
                    deos_view::ViewNode::Section { title, .. } if title == "Tool classes"
                )
            });
            assert!(
                has_menu,
                "the surface carries the cap-gated tool-class menu"
            );
        }
        other => panic!("a rendered surface must be a deos Section, got {other:?}"),
    }

    let report = off.verify(&s);
    assert!(
        report.verified,
        "the mixed confinement chain re-verifies: {}",
        report.detail
    );
    assert_eq!(report.turns, 5);
}

/// **The default swap — the offering wires the REAL `deos_hermes::ResidentBrain`.**
/// `HermesOffering::new()` (the DEPLOY constructor) resolves the real resident brain
/// seam (on-box by default, a live BYO-key brain when a provider key is set), while
/// `scripted()` pins the deterministic mock the enforcement tests use. Asserted
/// secret-free and with NO network call (only the seam label is read).
#[test]
fn the_default_offering_wires_the_real_resident_brain_seam() {
    let deployed = HermesOffering::new();
    let seam = deployed.brain_seam();
    assert!(
        seam.starts_with("resident:"),
        "the default brain seam is the real deos_hermes::ResidentBrain, got {seam:?}"
    );

    let mock = HermesOffering::scripted();
    assert_eq!(
        mock.brain_seam(),
        "scripted-mock",
        "the test constructor retains the deterministic mock brain"
    );
}
