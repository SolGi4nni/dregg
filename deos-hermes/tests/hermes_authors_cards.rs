//! THE HANDS THAT AUTHOR, PROVEN BY RUNNING — a confined Hermes agent AUTHORS the
//! cockpit's cards (create + edit), each a receipted, cap-gated view-patch, bounded by
//! its `held`, over-reach refused IN-BAND. The ADOS dream: the agent BUILDS the world it
//! inhabits, accountably.
//!
//! Run: `cd deos-hermes && cargo test --features js-agent --test hermes_authors_cards`
//! (the default `cargo test` is mozjs-free — the card-authoring path pulls deos-js via
//! the `js-agent` feature, like `run_js`.)
//!
//! Four things proven (the authoring sibling of `hermes_runs_js.rs`):
//!   (a) CREATE — the agent mints a fresh card from a manifest + authors its first button
//!       as a receipted patch; the new view carries the button; the gateway metered the
//!       `create_card` tool-call (the accountability turn).
//!   (b) EDIT — the agent patches an existing card's view (add a button) as a receipted
//!       patch; the `edit_card` tool-call is admitted + metered.
//!   (c) BLAME — every authored line is attributed to the AGENT'S `Author` (the agent
//!       acts as itself — the confused-deputy property, accountable).
//!   (d) OVER-REACH REFUSED — authoring a card whose `edit_authority` the agent's `held`
//!       does NOT satisfy is refused IN-BAND by the cap tooth (no patch, no receipt) —
//!       the SAME gate a human authoring goes through; the agent gets no wider authority.
//!
//! The `create_card` / `edit_card` tool-call ITSELF is admitted by the proven
//! `HermesGateway` as a scoped, rate-limited `ToolGrant` (the accountability turn); the
//! `CardEditor` mounts the agent's `held`, never root (the confinement invariant).

#![cfg(feature = "js-agent")]

use std::sync::{Arc, RwLock};

use deos_hermes::card_authoring::CardAuthoringTool;
use deos_hermes::{GrantRegistry, HermesGateway, ToolCallRequest};
use deos_js::card_editor::{BindProps, TextProps, ViewPatch, ViewTree};
use deos_js::portable::{AffordanceSpec, AppletManifest, ApplyOp, PortableApplet};
use dregg_cell::AuthRequired;
use dregg_cell::{Credential, Requirement};
use dregg_doc::Author;
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

/// deos the grantor: the runtime that admits the agent's authoring workers and runs their
/// accountability turns.
fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// A scoped, rate-limited session registry with the standard card-authoring grants (the
/// accountability mandates the gateway meters `create_card` / `edit_card` on).
fn session_registry() -> GrantRegistry {
    GrantRegistry::default_for_session(10_000).with_standard_tool_grants(10_000)
}

/// A counter card's manifest: a title + a live count bind, a `inc` affordance. The shape
/// `deos-view` paints; the agent authors a button onto it.
fn counter_manifest() -> AppletManifest {
    let view = ViewTree::VStack {
        children: vec![
            ViewTree::Text {
                props: TextProps {
                    text: "Counter".into(),
                },
            },
            ViewTree::Bind {
                props: BindProps {
                    slot: 0,
                    label: "count".into(),
                },
            },
        ],
    };
    AppletManifest {
        seed_fields: vec![(0usize, 0u64)],
        affordances: vec![AffordanceSpec {
            name: "inc".into(),
            required: Requirement::AtLeast(Credential::Signature),
            op: ApplyOp::AddToSlot { slot: 0 },
        }],
        held: AuthRequired::Signature,
        view_source: view.to_json(),
    }
}

// ── (a) CREATE + (c) BLAME ───────────────────────────────────────────────────────────
#[test]
fn agent_creates_a_card_authoring_its_first_button_as_a_receipted_patch() {
    let (rt, root) = grantor();
    let mut gw = HermesGateway::new(&rt, root, session_registry());

    // The agent holds a broad-but-attenuated mandate (None = single-custody) and authors
    // as itself (Author 99). The card requires Signature to author — the agent's held
    // satisfies it. This mirrors run_js mounting the editor under the agent's `held`.
    let tool = CardAuthoringTool::new(AuthRequired::None, Author(99));

    let mut pk = [0u8; 32];
    pk[0] = 0xCA;
    let call = ToolCallRequest::new(
        "s",
        "tc-create-1",
        "create_card",
        serde_json::json!({ "card": "counter" }),
    );

    let out = tool.create_card(
        &mut gw,
        &call,
        50,
        pk,
        [0u8; 32],
        counter_manifest(),
        /*edit_authority=*/ Requirement::AtLeast(Credential::Signature),
        Some(ViewPatch::AddButton {
            label: "+1".into(),
            turn: "inc".into(),
            arg: 1,
        }),
    );

    // The `create_card` tool-call itself was admitted accountably (a metered, receipted
    // ToolGrant turn) — the agent is granted its authoring hands this turn.
    assert!(
        out.tool_admitted(),
        "the create_card tool-call is admitted by the gateway (the accountability turn): {:?}",
        out.tool_outcome
    );
    assert_eq!(
        gw.calls_made_for_tool("create_card"),
        1,
        "the create_card call is metered — every authoring action is receipted, never free"
    );

    // (a) The authoring committed: a provenance receipt landed on the card's chain.
    assert!(
        out.authored(),
        "the agent authored the card (a provenance receipt landed): {:?}",
        out.refused_reason
    );
    assert!(
        out.provenance_receipt.is_some_and(|r| r != [0u8; 32]),
        "the structural view-edit left a real provenance receipt"
    );
    // The re-folded view carries the new button (the UI the agent built from within).
    let new_view = out
        .view_source
        .expect("authoring yields the new view source");
    let tree = ViewTree::from_json(&new_view).expect("the authored view is a parseable tree");
    assert!(
        tree.has_button_for("inc"),
        "the agent authored a card's UI from within — the +1 button is in the re-folded view"
    );

    // (c) BLAME — the authored line is attributed to the AGENT (Author 99). The agent
    // acts as itself; the patch is accountable to it.
    assert!(
        out.blamed_authors.contains(&99),
        "the agent's authoring patch is blamed on the agent (Author 99): {:?}",
        out.blamed_authors
    );
}

// ── (b) EDIT ─────────────────────────────────────────────────────────────────────────
#[test]
fn agent_edits_an_existing_cards_view_as_a_receipted_patch() {
    let (rt, root) = grantor();
    let mut gw = HermesGateway::new(&rt, root, session_registry());
    let tool = CardAuthoringTool::new(AuthRequired::None, Author(99));

    // An already-minted card the agent adopts + patches.
    let manifest = counter_manifest();
    let mut pk = [0u8; 32];
    pk[0] = 0xED;
    let card = PortableApplet::mint(pk, [0u8; 32], &manifest);

    let call = ToolCallRequest::new(
        "s",
        "tc-edit-1",
        "edit_card",
        serde_json::json!({ "patch": "add reset" }),
    );

    let out = tool.edit_card(
        &mut gw,
        &call,
        51,
        card,
        manifest,
        AuthRequired::Signature,
        ViewPatch::AddButton {
            label: "reset".into(),
            turn: "reset".into(),
            arg: 0,
        },
    );

    assert!(
        out.tool_admitted(),
        "edit_card is admitted (the accountability turn)"
    );
    assert_eq!(
        gw.calls_made_for_tool("edit_card"),
        1,
        "the edit_card call is metered"
    );
    assert!(
        out.authored(),
        "the agent's edit landed a receipted patch: {:?}",
        out.refused_reason
    );
    let tree = ViewTree::from_json(&out.view_source.unwrap()).unwrap();
    assert!(
        tree.has_button_for("reset"),
        "the agent edited the card's view — the reset button is in the re-folded view"
    );
}

// ── (d) OVER-REACH REFUSED — the bound the agent cannot exceed. ──────────────────────
#[test]
fn agent_cannot_author_a_card_outside_its_held_refused_in_band() {
    let (rt, root) = grantor();
    let mut gw = HermesGateway::new(&rt, root, session_registry());

    // The agent holds only SIGNATURE; the card requires PROOF to author — an over-reach.
    let tool = CardAuthoringTool::new(AuthRequired::Signature, Author(99));

    let manifest = counter_manifest();
    let mut pk = [0u8; 32];
    pk[0] = 0xBA;
    let card = PortableApplet::mint(pk, [0u8; 32], &manifest);

    let call = ToolCallRequest::new(
        "s",
        "tc-edit-over",
        "edit_card",
        serde_json::json!({ "patch": "add +1" }),
    );

    let out = tool.edit_card(
        &mut gw,
        &call,
        52,
        card,
        manifest,
        /*edit_authority=*/ Requirement::AtLeast(Credential::Proof),
        ViewPatch::AddButton {
            label: "+1".into(),
            turn: "inc".into(),
            arg: 1,
        },
    );

    // The tool-call ITSELF is still admitted (the agent IS granted edit_card — the bound
    // is on what it may AUTHOR, not on running the authoring tool at all). Mirrors
    // run_js's "granted, but the fire over-reach is refused" shape.
    assert!(
        out.tool_admitted(),
        "edit_card is granted (the bound is on the authoring, not on running the tool)"
    );
    // THE BOUND: the over-reach authored NOTHING. No patch, no receipt — the cap tooth
    // refused in-band, surfaced as a named reason.
    assert!(
        !out.authored(),
        "OVER-REACH HOLE — a Proof-gated card was authored by a Signature-held agent"
    );
    assert!(
        out.provenance_receipt.is_none(),
        "an over-reach leaves NO receipt — it never happened"
    );
    assert!(
        out.refused_reason
            .as_deref()
            .is_some_and(|r| r.contains("cap-gate") || r.contains("refused")),
        "the agent saw the cap-gate refusal in-band (a named reason): {:?}",
        out.refused_reason
    );
}
