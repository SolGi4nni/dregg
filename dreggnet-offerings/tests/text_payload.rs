//! **The `Action` text-payload round-trip** — the additive first-class free-text field, DRIVEN
//! through both wires it must survive:
//!
//! 1. **the deos affordance codec** (`deos_view::affordance`): a text-bearing affordance encodes
//!    and decodes losslessly (turn + arg + text) across every transport, while a text-free
//!    affordance is byte-identical to the pre-text codec;
//! 2. **a [`MockFrontend`] present -> collect**: the reference frontend presents a text-taking
//!    affordance and collects a press that supplies free text, reproducing the string on the
//!    collected [`Action::text`] — the actuation round-trip a real Discord/Telegram/web frontend
//!    performs, with no label-riding and no `askt`/`subt` side channel.
//!
//! This is the proof that the additive `Action::text` is genuinely carried by the affordance
//! transport, not merely stored — the gap that forced dreggnet-doc onto [`Action::label`] and the
//! discord-bot onto a companion modal wire is closed at the type it belongs to.

use deos_view::affordance::{
    AffordanceTransport, affordance_id, affordance_id_with_text, parse_affordance_id,
    parse_affordance_id_with_text,
};
use dreggnet_offerings::mock::{MockEvent, MockFrontend};
use dreggnet_offerings::{Action, Frontend, SessionId, Surface};

const ALL: [AffordanceTransport; 4] = [
    AffordanceTransport::Discord,
    AffordanceTransport::Telegram,
    AffordanceTransport::Web,
    AffordanceTransport::WeChat,
];

/// An empty surface to present affordances against (the round-trip is over the actions, not the
/// view-tree).
fn empty_surface() -> Surface {
    Surface(deos_view::ViewNode::VStack(Vec::new()))
}

/// A text-bearing affordance survives the codec on every transport; a text-free one is
/// byte-identical to the plain codec.
#[test]
fn a_text_bearing_action_round_trips_through_the_codec() {
    // A document paragraph carrying the codec's own separators + unicode: proof the text is held
    // opaquely, never mistaken for the `{turn, arg}` shape.
    let prose = "…continue: the dragon's hoard — 世界 :) a:b:c #hash";
    for t in ALL {
        // WITH text: turn + arg + text all survive.
        let id = affordance_id_with_text("insert", 3, Some(prose), t);
        assert_eq!(
            parse_affordance_id_with_text(&id, t),
            Some(("insert".to_string(), 3, Some(prose.to_string()))),
            "{t:?} carries turn+arg+text losslessly",
        );

        // WITHOUT text: byte-identical to the pre-text codec (the additive-non-breaking tooth).
        assert_eq!(
            affordance_id_with_text("insert", 3, None, t),
            affordance_id("insert", 3, t),
            "{t:?} text-free encode is byte-identical",
        );
        let plain = affordance_id("insert", 3, t);
        assert_eq!(
            parse_affordance_id_with_text(&plain, t),
            Some(("insert".to_string(), 3, None)),
            "{t:?} a plain id decodes with text: None",
        );
        assert_eq!(
            parse_affordance_id(&plain, t),
            Some(("insert".to_string(), 3)),
            "{t:?} the plain decoder still sees the plain id",
        );
    }
}

/// The reference frontend presents a text-taking affordance and collects a text-bearing press;
/// the free text the presser supplied is reproduced on the collected action. A text-free press is
/// unchanged, and a presented default text round-trips too.
#[test]
fn a_text_bearing_action_round_trips_through_a_mock_frontend() {
    let mut fe = MockFrontend::new();
    let sid = SessionId::new("doc-1");
    fe.spin_session(sid.clone());

    // The offering presents a text-taking insert affordance (its default text is None — the user
    // supplies the prose) beside a plain fixed-arg delete.
    let insert = Action::new("…continue the document", "insert", 3, true);
    let delete = Action::new("delete cell 1", "delete", 1, true);
    fe.present(&sid, &empty_surface(), &[insert, delete]);

    // A press that SUPPLIES free text (the modal field): collect reproduces turn + arg + text.
    let typed = "the dragon's hoard glittered in the torchlight";
    let (_, got, _) = fe
        .collect(MockEvent::press_text(&sid, "ann", "insert", 3, typed))
        .expect("the presented affordance collects");
    assert_eq!(got.turn, "insert");
    assert_eq!(got.arg, 3);
    assert_eq!(
        got.text.as_deref(),
        Some(typed),
        "the user's free text survives present -> collect",
    );

    // A TEXT-FREE press is byte-identical to the pre-text path: the collected action has no text.
    let (_, got, _) = fe
        .collect(MockEvent::press(&sid, "ann", "delete", 1))
        .expect("the plain affordance collects");
    assert_eq!(got.turn, "delete");
    assert_eq!(got.arg, 1);
    assert_eq!(
        got.text, None,
        "a text-free affordance collects with no text — unchanged from before",
    );

    // A presented affordance that ITSELF carries a default text (built with `with_text`) is
    // reproduced when the press supplies none — the presented payload round-trips as-is.
    let seeded = Action::new("send the prompt", "prompt", 0, true).with_text("draft prompt");
    fe.present(&sid, &empty_surface(), &[seeded]);
    let (_, got, _) = fe
        .collect(MockEvent::press(&sid, "ann", "prompt", 0))
        .expect("the seeded affordance collects");
    assert_eq!(
        got.text.as_deref(),
        Some("draft prompt"),
        "a presented default text round-trips through collect too",
    );
}

/// The end-to-end shape the two workarounds were faking: a text-bearing `Action` collected from a
/// frontend re-encodes onto the codec wire and decodes back to the SAME turn + arg + text — the
/// actuation carries its string first-class, from press to wire and back.
#[test]
fn a_collected_text_action_re_encodes_onto_the_codec_wire() {
    let mut fe = MockFrontend::new();
    let sid = SessionId::new("hermes-1");
    fe.spin_session(sid.clone());
    fe.present(
        &sid,
        &empty_surface(),
        &[Action::new("prompt the agent", "prompt", 0, true)],
    );

    let typed = "summarise the ledger since block 42:100 — briefly";
    let (_, action, _) = fe
        .collect(MockEvent::press_text(&sid, "ann", "prompt", 0, typed))
        .expect("collect");

    // The collected action's payload rides the codec (here: the web transport) and decodes back.
    let wire = affordance_id_with_text(
        &action.turn,
        action.arg,
        action.text.as_deref(),
        AffordanceTransport::Web,
    );
    assert_eq!(
        parse_affordance_id_with_text(&wire, AffordanceTransport::Web),
        Some(("prompt".to_string(), 0, Some(typed.to_string()))),
        "the collected text survives the codec wire end-to-end",
    );
}
