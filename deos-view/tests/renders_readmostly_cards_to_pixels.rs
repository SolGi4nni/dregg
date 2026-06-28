//! THE PROOF, BY RUNNING: three more cockpit surfaces — PROOFS (verification status),
//! ORGANS (live organ cell-state), and HOME (the landing portal) — are deos-js cards whose
//! view-trees render to REAL gpui-component pixels (a PNG each).
//!
//! These are the read-mostly surfaces the COCKPIT-LIBERATION-PLAN names as fitting today's
//! vocabulary. Each is built gpui-FREE in `deos-js` (`proofs_view` / `organs_view` /
//! `home_view`) and uses the authoring-mirror's batch-1 richness nodes — `section` + `pill`
//! — which bridge losslessly into `deos-view`'s `ViewNode::Section`/`ViewNode::Pill` and
//! paint through the SAME `parse_view_tree` + `AppletView` the other reflective-card proofs
//! use. The proof here is that the section/pill-carrying view-trees render to pixels.

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::applet::{pack_u64, Applet};
use deos_js::{HomeLine, HomeSection, OrganCardRow, ProofCardRow};
use dregg_cell::AuthRequired;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::{parse_view_tree, AppletView};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/render-out");
    std::fs::create_dir_all(&dir).expect("create render-out dir");
    dir
}

fn render_applet() -> Applet {
    Applet::mint(
        [0x5E; 32],
        [0u8; 32],
        &[(0usize, pack_u64(0))],
        Vec::new(),
        AuthRequired::None,
    )
}

#[test]
fn readmostly_cards_render_to_real_gpui_pixels() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(body)
        .expect("spawn big-stack render thread")
        .join()
        .expect("read-mostly-cards render proof thread");
}

fn body() {
    let out = out_dir();
    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");

    // PROOFS — a summary pill row + one tier-tinted section per turn.
    let proofs = deos_js::proofs_view(
        1,
        0,
        1,
        &[
            ProofCardRow {
                height: 2,
                receipt_short: "9f3a".into(),
                tier_label: "STARK-attached".into(),
                tag: "good".into(),
                summary: "h2 · STARK-attached · proof present · pre 11 → post 22".into(),
                route: None,
            },
            ProofCardRow {
                height: 1,
                receipt_short: "1c0d".into(),
                tier_label: "verified-by-construction".into(),
                tag: "muted".into(),
                summary: "h1 · verified-by-construction · re-exec · pre 00 → post 11".into(),
                route: Some("attach the executor signature".into()),
            },
        ],
    )
    .to_json();
    let proofs_png = render_to_png(&mut hr, &proofs, out.join("proofs-card.png"));

    // ORGANS — three sections (trustlines · flash wells · remote-path).
    let organs = deos_js::organs_view(
        2,
        1,
        &[OrganCardRow {
            glyph: "⬡".into(),
            short: "ab12 (trustline)".into(),
            summary: "line 1000 · drawn 400 · remaining 600".into(),
        }],
        &[OrganCardRow {
            glyph: "⬡".into(),
            short: "cd34 (flash well)".into(),
            summary: "principal 500 · fee 5 · accrued 12".into(),
        }],
        &[OrganCardRow {
            glyph: "◌".into(),
            short: "channel (remote)".into(),
            summary: "seam captp · route node".into(),
        }],
    )
    .to_json();
    let organs_png = render_to_png(&mut hr, &organs, out.join("organs-card.png"));

    // HOME — the masthead (liveness pills) + a section per portal section.
    let home = deos_js::home_view(
        "you have arrived",
        "a sovereign verified image is running",
        &[
            ("● live".into(), "good".into()),
            ("h7".into(), "accent".into()),
            ("4 cells".into(), "accent".into()),
        ],
        &[HomeSection {
            title: "THE VERIFIED HEART".into(),
            lines: vec![
                HomeLine {
                    text: "every turn runs the verified executor".into(),
                    heading: true,
                },
                HomeLine {
                    text: "a receipt's existence is its proof".into(),
                    heading: false,
                },
            ],
        }],
        "click anything to begin",
    )
    .to_json();
    let home_png = render_to_png(&mut hr, &home, out.join("home-card.png"));

    println!("RENDERED READ-MOSTLY-CARD PNGs (real gpui-component widgets, offscreen wgpu):");
    println!("  proofs : {}", proofs_png.display());
    println!("  organs : {}", organs_png.display());
    println!("  home   : {}", home_png.display());
}

/// Render a card's view-tree JSON over a live applet, capture a PNG, assert it has pixels.
fn render_to_png(hr: &mut HeadlessRender, source: &str, png: PathBuf) -> PathBuf {
    // The section/pill nodes must lift (the bridge); a parse failure fails the test.
    let tree = parse_view_tree(source).expect("parse the read-mostly card view-tree");
    let applet = Rc::new(RefCell::new(render_applet()));
    let window = hr
        .open(560.0, 900.0, move |_w, cx| {
            cx.new(|_cx| AppletView::new(applet, tree))
        })
        .expect("open the card window");
    let frame = hr.capture(window.into()).expect("capture the card frame");
    frame.save(&png).expect("save the card PNG");
    assert!(
        frame.width() > 0 && frame.height() > 0,
        "the frame has pixels"
    );
    png
}
