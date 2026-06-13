//! THE COMPOSITOR-PD BOOT TEST — two app-PDs composite to the framebuffer
//! through the compositor-PD; an overpaint is REFUSED; input routes to the
//! focused one (`docs/DREGG-DESKTOP-OS.md §2 L5` + `§6 R3 Stage D`).
//!
//! This is the §6 R3 Stage D slice, native-now on the semihost
//! [`EmulatedKernel`]: "Two app-PDs composite to screen, input routes to the
//! focused one (banscii artist's `region_in → composite → region_out → flush`,
//! generalized)." The no-amplification guarantee fires AT THE FRAMEBUFFER.
//!
//! ## The shape (generalizing banscii `region_in → composite → region_out → flush`)
//!
//! The compositor-PD is the Endpoint SERVER. Two app-PDs (a "wallet" and a
//! "browser", the Lean `demoScene` cells) are clients that `pp_call` the
//! compositor's present-endpoint with an encoded `present(region, contentDigest)`
//! (`region_in`); the compositor runs the scene-authority gate, composites the
//! authorized region into the framebuffer it SOLELY holds (`composite` →
//! `region_out`/`flush`), and replies the verdict. We prove, on ONE shared
//! EmulatedKernel:
//!
//!   1. **the wallet's HONEST present COMMITS** — its own region 10 advances; the
//!      framebuffer tile 10 reflects its digest (the COMMIT polarity);
//!   2. **the browser's HONEST present COMMITS** — its own region 20 advances
//!      (two app-PDs composite side-by-side);
//!   3. **the browser's OVERPAINT of the wallet's region 10 is REFUSED** — the T1
//!      tooth fires across the IPC boundary; tile 10 is UNCHANGED (the wallet's
//!      pixel is untouched — no-amplification at the framebuffer);
//!   4. **input routes to the FOCUSED wallet, and the browser stealing it is
//!      REFUSED** — the T3 input gate.
//!
//! ## Fidelity (honestly labeled — NOT laundered)
//!
//! The framebuffer is a HOST in-memory buffer (an EmulatedKernel region), NOT a
//! scanned-out panel — the compositor-PD enforces scene AUTHORITY (T1/T2/T3, the
//! teeth proven in the Lean `Dregg2.Apps.Compositor` AppSpec), and the pixels are
//! the renderer's. F1/F2/F3 (last-hop frame attestation, IOMMU/DMA confinement,
//! verified GPU) are the named graphics frontier (R3 Stage C), NOT solved here.
//! The honest label travels with the code: [`CompositorPd::FIDELITY`].

use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

use dregg_firmament::compositor_pd::{
    cell_seed, encode_present, label_of, CompositorPd, Present, Scene, Surface, LABEL_PRESENT,
    LABEL_PRESENT_OK, LABEL_PRESENT_REFUSED,
};
use dregg_firmament::emulated_kernel::EmulatedKernel;
use dregg_firmament::microkit_facade::{Channel, ChannelTable, ChannelWiring, MessageInfo};

/// The honest two-surface scene from the Lean `demoScene`: wallet (regions
/// {10,11}, root 500, FOCUSED) + browser (regions {20,21}, root 600). The
/// compositor cell holds this as its state; the shell (L6) composed it.
fn demo_scene() -> Scene {
    Scene {
        surfaces: vec![
            Surface {
                owner: cell_seed(1), // the wallet
                regions: vec![10, 11],
                content_digest: 0, // un-composited (the framebuffer starts blank)
                source_state_root: 500,
                z_layer: 0,
                focus_flag: true, // the wallet holds focus
            },
            Surface {
                owner: cell_seed(2), // the browser
                regions: vec![20, 21],
                content_digest: 0,
                source_state_root: 600,
                z_layer: 0,
                focus_flag: false,
            },
        ],
    }
}

// ===========================================================================
// THE BOOT TEST — two app-PDs composite through the compositor-PD over the
// Endpoint; the overpaint is refused at the framebuffer; input is routed.
//
// The compositor-PD runs on its own host thread as the Endpoint SERVER (a real
// PD's `protected` body on its own thread), serving exactly the calls the two
// app-PDs make. The app-PDs are client threads that `Channel::pp_call` the
// present-endpoint. ONE EmulatedKernel; the framebuffer + scene live in the
// compositor-PD, behind the gate. This is the same-code boot shape as
// boot_pds.rs (PDs are threads over one kernel), now exercising the §3 Endpoint
// (pp_call) path and the L5 compositor multiplexer.
// ===========================================================================

#[test]
fn two_pds_composite_overpaint_refused_input_routed() {
    // ── The firmament wires the slice at boot (the `.system`-file equivalent). ──
    let kernel = EmulatedKernel::new();
    let wallet = cell_seed(1);
    let browser = cell_seed(2);

    // The present-endpoint both app-PDs pp_call (the compositor's PP channel).
    let present_ep = kernel.create_endpoint();
    const PRESENT_CHANNEL: usize = 7;

    // The compositor-PD boots: it allocates + SOLELY holds the framebuffer
    // region and starts with the demo scene. It is shared (behind a Mutex) ONLY
    // so the harness can read the framebuffer/log AFTER the threads join — the
    // compositor's OWN thread is the sole writer during the slice (the server
    // thread holds the lock across each served call; the harness never contends
    // while a call is in flight because it reads only after the join). On a real
    // PD the compositor IS its thread; here the Arc<Mutex> is the harness's
    // observation handle, not a second authority.
    let compositor = Arc::new(Mutex::new(CompositorPd::boot(kernel.clone(), demo_scene())));

    // ── The compositor-PD server thread: serve exactly FOUR present() calls
    //    (wallet-honest, browser-honest, browser-overpaint, wallet-second), then
    //    return. Each `serve_present` blocks on the Endpoint until an app-PD
    //    calls, runs the gate + composite, and replies the verdict. ──
    let comp_srv = compositor.clone();
    let server = thread::spawn(move || {
        for _ in 0..4 {
            let mut c = comp_srv.lock().unwrap();
            // Block until an app-PD pp_calls; gate + composite + reply.
            let _verdict = c.serve_present(present_ep).expect("serve present");
            drop(c);
        }
    });

    // Give the server a beat to park on `recv` (not load-bearing — the rendezvous
    // blocks either way — but exercises the genuine Endpoint synchrony).
    thread::sleep(Duration::from_millis(20));

    // ── App-PD wiring: each app names the present-channel (index → endpoint). ──
    let mut app_table = ChannelTable::new();
    app_table.wire(
        PRESENT_CHANNEL,
        ChannelWiring { notification: kernel.create_notification(), endpoint: Some(present_ep) },
    );
    let app_table = Arc::new(app_table);

    // A small helper: an app-PD submits a present() over the Endpoint and returns
    // the reply label (OK / REFUSED) — the `region_in → … → reply` shape.
    let submit = |presenter: &_, p: &Present| -> u64 {
        let ch = Channel::bound(PRESENT_CHANNEL, kernel.clone(), app_table.clone());
        let bytes = encode_present(presenter, p);
        let (reply_tag, _reply_bytes) = ch
            .pp_call(MessageInfo::new(LABEL_PRESENT, bytes.len()), &bytes)
            .expect("present pp_call round-trips");
        reply_tag.label()
    };

    // ── PD-WALLET: the HONEST present — paints its OWN region 10, declares its
    //    GENUINE label, claims focus (it IS the focus holder). COMMITS. ──
    let wallet_honest = Present {
        target: vec![10],
        source_state_root: 500,
        declared_label: label_of(&wallet, 500),
        claims_focus: true,
        new_digest: 0xA1, // the wallet's frame
    };
    let r1 = submit(&wallet, &wallet_honest);
    assert_eq!(r1, LABEL_PRESENT_OK, "the wallet's honest present must COMMIT");

    // ── PD-BROWSER: the HONEST present — paints its OWN region 20, genuine
    //    label, no focus. COMMITS (two app-PDs composite side-by-side). ──
    let browser_honest = Present {
        target: vec![20],
        source_state_root: 600,
        declared_label: label_of(&browser, 600),
        claims_focus: false,
        new_digest: 0xB2, // the browser's frame
    };
    let r2 = submit(&browser, &browser_honest);
    assert_eq!(r2, LABEL_PRESENT_OK, "the browser's honest present must COMMIT");

    // ── PD-BROWSER: the OVERPAINT — targets region 10, which the WALLET owns
    //    (T1 violation). REFUSED at the framebuffer; the wallet's tile is
    //    untouched (no-amplification fires AT THE FRAMEBUFFER). ──
    let browser_overpaint = Present {
        target: vec![10], // ← the WALLET's region!
        source_state_root: 600,
        declared_label: label_of(&browser, 600),
        claims_focus: false,
        new_digest: 0xEE, // the attacker's would-be pixel
    };
    let r3 = submit(&browser, &browser_overpaint);
    assert_eq!(
        r3, LABEL_PRESENT_REFUSED,
        "the browser OVERPAINTING the wallet's region 10 must be REFUSED (T1)"
    );

    // ── PD-WALLET: a second honest present (so the server's 4th serve completes
    //    and the thread returns cleanly). ──
    let wallet_second = Present {
        target: vec![11],
        source_state_root: 501,
        declared_label: label_of(&wallet, 501),
        claims_focus: false,
        new_digest: 0xA3,
    };
    let r4 = submit(&wallet, &wallet_second);
    assert_eq!(r4, LABEL_PRESENT_OK, "the wallet's second present must COMMIT");

    // ── Join the server (all four calls served). ──
    server.join().expect("compositor-PD served all presents");

    // ── THE FRAMEBUFFER OBSERVABLE (the compositor SOLELY holds it). ──
    let comp = compositor.lock().unwrap();
    let fb = comp.framebuffer_snapshot();

    // Tile 10 = the WALLET's first frame (0xA1) — the honest present composited.
    // Crucially it is NOT 0xEE: the browser's overpaint NEVER reached the pixel.
    assert_eq!(fb[10], 0xA1, "tile 10 holds the WALLET's frame — the overpaint never composited");
    assert_ne!(fb[10], 0xEE, "the attacker's pixel must NOT be at the wallet's tile 10");
    // Tile 20 = the BROWSER's frame (0xB2) — its own region composited.
    assert_eq!(fb[20], 0xB2, "tile 20 holds the BROWSER's frame (its own region)");
    // Tile 11 = the WALLET's second frame (0xA3).
    assert_eq!(fb[11], 0xA3, "tile 11 holds the wallet's second frame");

    // ── THE FRAME LOG: exactly the THREE committed presents (the refusal logged
    //    NOTHING — fail-closed). ──
    assert_eq!(comp.frames().len(), 3, "three presents COMMITTED; the overpaint logged nothing");
    assert_eq!(comp.present_count(&wallet), 2, "the wallet committed two presents");
    assert_eq!(comp.present_count(&browser), 1, "the browser committed one (its honest present)");

    // ── THE T3 INPUT GATE: input routes to the FOCUSED wallet; the browser
    //    stealing it is REFUSED. ──
    assert_eq!(
        comp.route_input(&wallet).expect("input routes to the focus holder"),
        wallet,
        "input is delivered to the focused wallet"
    );
    assert!(
        comp.route_input(&browser).is_err(),
        "the non-focused browser cannot steal input (T3 input-misroute)"
    );

    // The honest fidelity label travels with the code (it is NOT verified graphics).
    assert!(
        CompositorPd::FIDELITY.contains("SCENE AUTHORITY"),
        "the fidelity label states the compositor enforces authority, not pixels"
    );

    println!(
        "COMPOSITOR-PD: two app-PDs composited (wallet tile 10=0x{:02X}, browser tile 20=0x{:02X}); \
         the browser's OVERPAINT of the wallet's region 10 was REFUSED (tile 10 still 0x{:02X}, not \
         0xEE); input routed to the focused wallet. no-amplification fired at the framebuffer ( ◕‿◕ )",
        fb[10], fb[20], fb[10]
    );
}

// ===========================================================================
// THE INLINE PATH — the same gate, single-threaded (no second thread). This
// exercises the compositor's protected body via `serve_present_inline` over a
// staged call, so the slice runs deterministically with no thread timing. It
// also drives the DOUBLE-FOCUS tooth (an ambiguous scene refuses every present).
// ===========================================================================

#[test]
fn inline_present_gate_commit_and_every_tooth() {
    let kernel = EmulatedKernel::new();
    let wallet = cell_seed(1);
    let browser = cell_seed(2);
    let mut comp = CompositorPd::boot(kernel, demo_scene());

    use dregg_firmament::emulated_kernel::Message;

    // HONEST: the wallet paints its own region 10 — COMMITS (the inline serve).
    let honest = encode_present(
        &wallet,
        &Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: true,
            new_digest: 0xA1,
        },
    );
    let reply = comp.serve_present_inline(Message::new(LABEL_PRESENT, honest));
    assert_eq!(reply.label, LABEL_PRESENT_OK, "honest present commits (inline)");
    assert_eq!(comp.framebuffer_snapshot()[10], 0xA1, "tile 10 composited");

    // T1 OVERPAINT: the browser targets the wallet's region 10 — REFUSED.
    let overpaint = encode_present(
        &browser,
        &Present {
            target: vec![10],
            source_state_root: 600,
            declared_label: label_of(&browser, 600),
            claims_focus: false,
            new_digest: 0xEE,
        },
    );
    let reply = comp.serve_present_inline(Message::new(LABEL_PRESENT, overpaint));
    assert_eq!(reply.label, LABEL_PRESENT_REFUSED, "overpaint refused (T1)");
    assert_eq!(reply.bytes[0], 1, "the refusal discriminant is T1 Overpaint");
    assert_eq!(comp.framebuffer_snapshot()[10], 0xA1, "tile 10 UNCHANGED by the refused overpaint");

    // T2 LABEL-SPOOF: the browser paints its own region 20 but DECLARES the
    // wallet's label — REFUSED.
    let spoof = encode_present(
        &browser,
        &Present {
            target: vec![20],
            source_state_root: 600,
            declared_label: label_of(&wallet, 500), // ← the wallet's label!
            claims_focus: false,
            new_digest: 0xB2,
        },
    );
    let reply = comp.serve_present_inline(Message::new(LABEL_PRESENT, spoof));
    assert_eq!(reply.label, LABEL_PRESENT_REFUSED, "label-spoof refused (T2)");
    assert_eq!(reply.bytes[0], 2, "the refusal discriminant is T2 LabelSpoof");

    // T3 INPUT-MISROUTE: the non-focused browser asserts focus to steal a
    // keystroke — REFUSED.
    let steal = encode_present(
        &browser,
        &Present {
            target: vec![20],
            source_state_root: 600,
            declared_label: label_of(&browser, 600),
            claims_focus: true, // ← the browser is NOT the focus holder!
            new_digest: 0xB2,
        },
    );
    let reply = comp.serve_present_inline(Message::new(LABEL_PRESENT, steal));
    assert_eq!(reply.label, LABEL_PRESENT_REFUSED, "input-misroute refused (T3)");
    assert_eq!(reply.bytes[0], 3, "the refusal discriminant is T3 InputMisroute");

    // T3 DOUBLE-FOCUS: against an ambiguous two-focus scene, every present is
    // refused (the scene itself routes input ambiguously).
    comp.set_scene(Scene {
        surfaces: vec![
            Surface { owner: wallet, regions: vec![10], content_digest: 0xA1, source_state_root: 500, z_layer: 0, focus_flag: true },
            Surface { owner: browser, regions: vec![20], content_digest: 0xB2, source_state_root: 600, z_layer: 0, focus_flag: true },
        ],
    });
    let honest_again = encode_present(
        &wallet,
        &Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: false,
            new_digest: 0xA9,
        },
    );
    let reply = comp.serve_present_inline(Message::new(LABEL_PRESENT, honest_again));
    assert_eq!(reply.label, LABEL_PRESENT_REFUSED, "double-focus scene refuses every present (T3)");
    assert_eq!(reply.bytes[0], 4, "the refusal discriminant is T3 DoubleFocus");

    // Only the ONE honest present committed; every tooth bit.
    assert_eq!(comp.frames().len(), 1, "only the honest present logged a frame");
}
