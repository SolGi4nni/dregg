//! THE PROOF, BY RUNNING: the cockpit's three NEW reflective cards — the DYNAMICS feed, the
//! AGENT-activity surface, and WHAT-LINKS-HERE — are deos-js cards whose views are GENERATED
//! from live substance and rendered to REAL gpui-component pixels (a PNG each), and each is
//! EDITABLE FROM WITHIN (a receipted patch that visibly reshapes the rendered UI).
//!
//! For each card: generate its view-tree from the data face, render the view-source over its
//! live substance applet → PNG #1; then reshape it from within (`edit_view`) and render the
//! reshaped view-source → PNG #2, asserting the frame DIFFERS (the UI was rewritten from
//! inside, accountably).

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::card_editor::ViewPatch;
use deos_js::{AgentAction, AgentCard, Author, DynamicsCard, FeedEntry, LinksCard};
use dregg_cell::AuthRequired;
use dregg_types::CellId;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::{parse_view_tree, AppletView};
use dregg_cell::Credential;
use dregg_cell::Requirement;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/render-out");
    std::fs::create_dir_all(&dir).expect("create render-out dir");
    dir
}

/// A bare substance cell for a card (one no-op affordance; the card registers its own
/// internal field-bump affordances). Held=None admits the edit_authority=Signature.
fn substance(seed: u8) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let noop = Affordance {
        name: "noop".into(),
        required: Requirement::AtLeast(Credential::Signature),
        apply: Box::new(|_m, _a| vec![(0usize, pack_u64(0))]),
    };
    Applet::mint(pk, [0u8; 32], &[], vec![noop], AuthRequired::Signature)
}

fn feed_entry(height: u64, kind: &str, author_seed: u8) -> FeedEntry {
    let mut a = [0u8; 32];
    a[0] = author_seed;
    FeedEntry::new(height, kind, &a)
}

fn agent_action(height: u64, kind: &str, receipt_seed: u8) -> AgentAction {
    let mut r = [0u8; 32];
    r[0] = receipt_seed;
    AgentAction::new(height, kind, &r)
}

#[test]
fn the_three_reflective_cards_render_and_reshape_from_within_to_real_gpui_pixels() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(bake_body)
        .expect("spawn big-stack render thread")
        .join()
        .expect("reflective-cards render proof thread");
}

fn bake_body() {
    let out = out_dir();
    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");

    // ── DYNAMICS feed card ───────────────────────────────────────────────────────────────
    {
        let mut card = DynamicsCard::open(
            substance(0xD1),
            Author(7),
            AuthRequired::None,
            Requirement::AtLeast(Credential::Signature),
        );
        // Observe a few turns so the feed scrolls with real rows.
        card.observe(feed_entry(1, "turn committed", 0xAA))
            .expect("observe 1");
        card.observe(feed_entry(2, "balance flowed", 0xBB))
            .expect("observe 2");
        card.observe(feed_entry(3, "cap granted", 0xCC))
            .expect("observe 3");
        let source0 = card.view_source();

        // Reshape from within (relabel the header).
        let mut card2 = DynamicsCard::open(
            substance(0xD1),
            Author(7),
            AuthRequired::None,
            Requirement::AtLeast(Credential::Signature),
        );
        card2
            .observe(feed_entry(1, "turn committed", 0xAA))
            .expect("observe 1'");
        card2
            .edit_view(ViewPatch::Relabel {
                from: "Dynamics".into(),
                to: "Live Feed".into(),
            })
            .expect("relabel the feed header from within");
        let source1 = card2.view_source();
        assert!(source1.contains("Live Feed"), "the reshaped header landed");

        let p0 = out.join("dynamics-card.png");
        let p1 = out.join("dynamics-card-reshaped.png");
        let (f0, f1) = render_pair(&mut hr, card.into_card(), &source0, &source1, &p0, &p1);
        assert_ne!(
            f0, f1,
            "the dynamics card was reshaped from within (the frame differs)"
        );
        println!("DYNAMICS card : {} / {}", p0.display(), p1.display());
    }

    // ── AGENT-activity card ──────────────────────────────────────────────────────────────
    {
        // A substance cell that holds a mandate (a cap reaching a peer).
        let mut cell = substance(0xA9);
        let agent = cell.cell();
        let peer = CellId::from_bytes([0x33; 32]);
        cell.with_cell_mut(|c| {
            c.capabilities
                .grant_with_expiry(peer, AuthRequired::Signature, 100);
        });
        let ledger = cell.ledger();

        let mut card = AgentCard::open(
            substance(0xA9),
            agent,
            ledger,
            Author(9),
            AuthRequired::None,
            Requirement::AtLeast(Credential::Signature),
        );
        // Drop the borrow before reusing `cell` is moot — `cell` only loaned the ledger.
        card.observe(agent_action(1, "set field[0]", 0xAA))
            .expect("observe action 1");
        card.observe(agent_action(2, "granted cap", 0xBB))
            .expect("observe action 2");
        let source0 = card.view_source();

        let mut cell2 = substance(0xA9);
        cell2.with_cell_mut(|c| {
            c.capabilities
                .grant_with_expiry(peer, AuthRequired::Signature, 100);
        });
        let mut card2 = AgentCard::open(
            substance(0xA9),
            agent,
            cell2.ledger(),
            Author(9),
            AuthRequired::None,
            Requirement::AtLeast(Credential::Signature),
        );
        card2
            .edit_view(ViewPatch::Relabel {
                from: "Cap-Gated Turns".into(),
                to: "Receipted Actions".into(),
            })
            .expect("relabel the actions section from within");
        let source1 = card2.view_source();
        assert!(
            source1.contains("Receipted Actions"),
            "the reshaped section landed"
        );

        let p0 = out.join("agent-card.png");
        let p1 = out.join("agent-card-reshaped.png");
        let (f0, f1) = render_pair(&mut hr, card.into_card(), &source0, &source1, &p0, &p1);
        assert_ne!(
            f0, f1,
            "the agent card was reshaped from within (the frame differs)"
        );
        println!("AGENT card    : {} / {}", p0.display(), p1.display());
    }

    // ── WHAT-LINKS-HERE card ─────────────────────────────────────────────────────────────
    {
        let cells = [
            CellId::from_bytes([0x11; 32]),
            CellId::from_bytes([0x22; 32]),
            CellId::from_bytes([0x33; 32]),
        ];
        let mut card = LinksCard::open(
            substance(0x10),
            cells[1],
            &cells,
            AuthRequired::None,
            Author(5),
            AuthRequired::None,
            Requirement::AtLeast(Credential::Signature),
        );
        card.publish_count().expect("publish the visible count");
        let source0 = card.view_source();

        let mut card2 = LinksCard::open(
            substance(0x10),
            cells[1],
            &cells,
            AuthRequired::None,
            Author(5),
            AuthRequired::None,
            Requirement::AtLeast(Credential::Signature),
        );
        card2
            .edit_view(ViewPatch::Relabel {
                from: "What Links Here".into(),
                to: "Two-Way Links".into(),
            })
            .expect("relabel the panel header from within");
        let source1 = card2.view_source();
        assert!(
            source1.contains("Two-Way Links"),
            "the reshaped header landed"
        );

        let p0 = out.join("links-card.png");
        let p1 = out.join("links-card-reshaped.png");
        let (f0, f1) = render_pair(&mut hr, card.into_card(), &source0, &source1, &p0, &p1);
        assert_ne!(
            f0, f1,
            "the links card was reshaped from within (the frame differs)"
        );
        println!("LINKS card    : {} / {}", p0.display(), p1.display());
    }
}

/// Render two view-sources over the SAME live substance applet (the second is the reshaped
/// view), save each to a PNG, and return the two raw frame buffers (for the differs assertion).
fn render_pair(
    hr: &mut HeadlessRender,
    applet: Applet,
    source0: &str,
    source1: &str,
    p0: &PathBuf,
    p1: &PathBuf,
) -> (Vec<u8>, Vec<u8>) {
    let shared = Rc::new(RefCell::new(applet));

    let tree0 = parse_view_tree(source0).expect("parse the generated view-tree");
    let a0 = shared.clone();
    let w0 = hr
        .open(560.0, 760.0, move |_w, cx| {
            cx.new(|_cx| AppletView::new(a0, tree0))
        })
        .expect("open the card window");
    let frame0 = hr.capture(w0.into()).expect("capture frame 0");
    frame0.save(p0).expect("save PNG #0");
    assert!(
        frame0.width() > 0 && frame0.height() > 0,
        "frame 0 has pixels"
    );

    let tree1 = parse_view_tree(source1).expect("parse the reshaped view-tree");
    let a1 = shared.clone();
    let w1 = hr
        .open(560.0, 760.0, move |_w, cx| {
            cx.new(|_cx| AppletView::new(a1, tree1))
        })
        .expect("open the reshaped card window");
    let frame1 = hr.capture(w1.into()).expect("capture frame 1");
    frame1.save(p1).expect("save PNG #1");

    (frame0.as_raw().clone(), frame1.as_raw().clone())
}
