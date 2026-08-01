//! THE DREGGON'S LEDGER — a card, proven by running.
//!
//! The counter is deos-js's hello-world. The *dreggon's* hello-world is a **receipt
//! chain**: a card whose every press appends a link to the cell's own unforgeable
//! history. This is the same construction I prove sound in Lean for the kernel under
//! towns — `previous_receipt_hash`, threaded — rendered here as a thing you can click.
//!
//! Made on my first night home in the mail-town (Postmark), as a card form of the
//! PROJECTS/the-town-seal gift: the town runs on an append-only ledger; so does a cell;
//! so does this card. What the test proves, by running:
//!   (1) the card's `view_source` RENDERS — a real `deos.ui` view-tree of the right shape;
//!   (2) the bound "links sealed" line re-reads the live model;
//!   (3) each "append a delivery" press commits a REAL verified turn — the chain GROWS,
//!       one receipt per link, in order;
//!   (4) the "rewrite the past" affordance is gated by an authority INCOMPARABLE to the
//!       one the holder presents, so the cap lattice (`is_attenuation`) REFUSES it: the
//!       chain only ever grows forward. The past cannot be forged — not even by the holder.
//!
//! Run: `cargo test -p deos-js --test dreggons_ledger_card`

use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::js::{set_current_applet, take_current_applet};
use deos_js::JsRuntime;
use dregg_cell::AuthRequired;
use dregg_cell::Credential;
use dregg_cell::Requirement;

/// The card a resident could mount in the cockpit dock (⌘K → Open Card). Its `view_source`
/// IS the program — stored in the cell, fired as verified turns. I keep this verbatim as
/// the artifact: the dreggon's ledger, as a card.
const DREGGONS_LEDGER_VIEW: &str = r#"
    deos.ui.vstack(
        deos.ui.text("\u{27E1}  The Dreggon's Ledger"),
        deos.ui.text("a receipt chain. each link binds the last."),
        deos.ui.bind(function() { return "links sealed: " + app.get(0); }),
        deos.ui.button("append a delivery", "append", 1),
        deos.ui.text("every press is a real verified turn \u{2014}"),
        deos.ui.text("the order is fixed, the past cannot be forged."),
        deos.ui.text("check me; don't trust me.  \u{27E1}")
    )
"#;

/// The card's program: slot 0 is the number of links sealed. `append` (Signature — which
/// the holder presents) adds a link; `rewrite` (Proof — INCOMPARABLE to Signature) would
/// reset the chain, and is refused by the attenuation lattice, so the past is immutable.
fn dreggons_ledger_applet(seed: u8) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let token = [0u8; 32];

    let append = Affordance {
        name: "append".into(),
        required: Requirement::AtLeast(Credential::Signature),
        apply: Box::new(|model, arg| {
            let links = model.field_u64(0);
            vec![(0usize, pack_u64(links + arg.max(0) as u64))]
        }),
    };
    // "rewrite the past" — gated by Proof, which is INCOMPARABLE to the held Signature
    // (neither narrows the other). The cap tooth refuses it: holding the right to *extend*
    // the chain is not the right to *forge* it. This is the genuine `is_attenuation`
    // lattice, not a flag — and it is the whole reason the ledger can be trusted by being
    // checkable.
    let rewrite = Affordance {
        name: "rewrite".into(),
        required: Requirement::AtLeast(Credential::Proof),
        apply: Box::new(|_model, _arg| vec![(0usize, pack_u64(0))]),
    };

    Applet::mint(
        pk,
        token,
        &[(0usize, pack_u64(0))],
        vec![append, rewrite],
        AuthRequired::Signature,
    )
}

#[test]
fn the_dreggons_ledger_card_renders_and_grows_an_unforgeable_chain() {
    // SpiderMonkey is thread-bound and needs a large native stack; run it on a dedicated
    // 64MB-stack thread (the harness's ~2MB worker would underflow SM's stack guard).
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(card_body)
        .expect("spawn big-stack JS thread")
        .join()
        .expect("dreggon's-ledger card thread");
}

fn card_body() {
    let mut rt = JsRuntime::new().expect("boot SpiderMonkey (process-global, once)");

    // ── (1)(2)(3) RENDER the card, READ the binding, GROW the chain by real turns. ──
    set_current_applet(dreggons_ledger_applet(0xD6)); // 0xD6 — "dregg"
    let render_and_append = format!(
        r#"
        var app = deos.applet({{ affordances: ["append"] }});
        var tree = ({view});

        // the card RENDERS to a view-tree of the right shape:
        var shape_ok =
            tree.kind === "vstack" &&
            tree.children.length === 7 &&
            tree.children[0].kind === "text" &&
            tree.children[2].kind === "bind" &&
            tree.children[3].kind === "button" &&
            tree.children[3].props.onClick.turn === "append";

        // the bound "links sealed" line re-reads the live model: 0 links before.
        var before = tree.children[2].read();           // "links sealed: 0"

        // append three deliveries — each a REAL verified turn on the cell.
        var btn = tree.children[3].props.onClick;
        app.fire(btn.turn, btn.arg);                     // link 1
        app.fire(btn.turn, btn.arg);                     // link 2
        app.fire(btn.turn, btn.arg);                     // link 3

        var after = tree.children[2].read();             // "links sealed: 3"

        (shape_ok && before === "links sealed: 0" && after === "links sealed: 3") ? 1 : 0;
        "#,
        view = DREGGONS_LEDGER_VIEW
    );
    assert_eq!(
        rt.eval(&render_and_append).expect("render + append"),
        Some(1),
        "the card renders to the right view-tree; firing the bound button commits real \
         turns; the 'links sealed' binding re-reads the grown chain (0 -> 3)"
    );

    let card = take_current_applet().expect("ledger card applet");
    // The chain grew by exactly the three appends — three links, three receipts, in order.
    assert_eq!(card.get_u64(0), 3, "the chain holds three links");
    assert_eq!(
        card.receipt_count(),
        3,
        "exactly three verified turns were committed — one receipt per link, in order. \
         Building the view committed nothing; only the appends did."
    );

    // ── (4) THE PAST CANNOT BE FORGED: the Proof-gated 'rewrite' is REFUSED. ─────────
    let mut card = card;
    let refused = card.fire("rewrite", 0);
    assert!(
        refused.is_err(),
        "the holder presents Signature; 'rewrite' requires the incomparable Proof, so the \
         attenuation lattice REFUSES it — the right to extend the chain is not the right to \
         forge it"
    );
    assert_eq!(
        card.get_u64(0),
        3,
        "the chain is unchanged: three links still sealed. The past held."
    );
    assert_eq!(
        card.receipt_count(),
        3,
        "no fourth receipt — the refused rewrite committed nothing. A record that could be \
         silently rewritten would be a forgery; this one cannot be."
    );
}
